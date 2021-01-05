#include "api.h"
#include "analysis.h"
#include "memory.h"
#include "solver.h"
#include "thread_context.h"
#include "syscall_context.h"

#define CLEAR_EFLAGS_AC(eflags)	((eflags & 0xfffbffff))

namespace qsym {

extern Memory       g_memory;
extern REG          g_thread_context_reg;
extern Solver        *g_solver;


bool kDynLdLnkLoaded = false;

static void
loadImage(IMG img, VOID* v) {
  LOG_INFO("IMG: " + IMG_Name(img) + "\n");
  if (kDynLdLnkLoaded)
    return;
  // //根据img加载的地址空间的length(最高-最低)，申请了length*sizeof(expref)大小的可读可写内存区域，相当于设定了符号区域？
  g_memory.mmap(IMG_LowAddress(img), IMG_HighAddress(img));
  //初始化了brk_start和end：最高地址对pageszie取余
  g_memory.initializeBrk(IMG_HighAddress(img));
	//这里逻辑似乎有点问题
    //第一个条件判定加载的有没有/lib/ld-linux.so.2 来判定是否动态链接 合理
    //第二个条件判定type是否等于IMG_TYPE_STATIC  不是判定是否静态吗？
	if (IMG_Name(img).compare("/lib/ld-linux.so.2") == 0 ||
			IMG_Type(img) == IMG_TYPE_STATIC)
    kDynLdLnkLoaded = true;
}

// from libdft
// global handler for internal errors (i.e., errors from qsym)
// handle memory protection (e.g., R/W/X access to null_seg)
// -- or --
// for unknown reasons, when an analysis function is executed,
// the EFLAGS.AC bit (i.e., bit 18) is asserted, thus leading
// into a runtime exception whenever an unaligned read/write
// is performed from qsym. This callback can be registered
// with PIN_AddInternalexceptionHandler() so as to trap the
// generated signal and remediate
//全局错误处理程序
static EXCEPT_HANDLING_RESULT
exceptionHandler(THREADID tid, EXCEPTION_INFO *pExceptInfo,
		PHYSICAL_CONTEXT *pPhysCtxt, VOID *v) {
	ADDRINT vaddr = 0x0;

	// unaligned memory accesses
	if (PIN_GetExceptionCode(pExceptInfo) ==
			EXCEPTCODE_ACCESS_MISALIGNED) {
		// clear EFLAGS.AC
		PIN_SetPhysicalContextReg(pPhysCtxt, REG_EFLAGS,
			CLEAR_EFLAGS_AC(PIN_GetPhysicalContextReg(pPhysCtxt,
					REG_EFLAGS)));

		// the exception is handled gracefully
		return EHR_HANDLED;
	}
	// memory protection
	else if (PIN_GetExceptionCode(pExceptInfo) ==
			EXCEPTCODE_ACCESS_DENIED) {

		// get the address of the memory violation
		PIN_GetFaultyAccessAddress(pExceptInfo, &vaddr);

    if (g_memory.isUnmappedAddress(vaddr)) {
      std::cerr << "invalid access -- memory protection triggered\n";
      exit(0);
    }
	}
	return EHR_UNHANDLED;
}

//每个线程开始时执行，将会new一个上下文对象， 存入g_thread_context_reg 寄存器类型变量中
static inline void
allocateThreadContext(THREADID tid, CONTEXT* ctx, INT32 flags, VOID* v) {
  g_memory.allocateStack(PIN_GetContextReg(ctx, REG_STACK_PTR));
  ThreadContext* thread_ctx = new ThreadContext();
  PIN_SetContextReg(ctx, g_thread_context_reg, (ADDRINT)thread_ctx);
}

//每个线程结束时执行   获取g_thread_context_reg寄存器的值，并释放掉（这是干啥？）
static inline void
freeThreadContext(THREADID tid, const CONTEXT* ctx, INT32 code, VOID* v) {
  ThreadContext* thread_ctx =
    reinterpret_cast<ThreadContext*>(PIN_GetContextReg(ctx, g_thread_context_reg));
  delete thread_ctx;
}

static inline void
initializeThreadContext() {
	if ((g_thread_context_reg = PIN_ClaimToolRegister()) == REG_INVALID())
    LOG_FATAL("register claim failed\n");

	//线程开始时插入回调函数
	PIN_AddThreadStartFunction(allocateThreadContext, NULL);
	//线程结束时插入回调函数
	PIN_AddThreadFiniFunction(freeThreadContext,	NULL);
}

static inline void
initializeMemory() {
  g_memory.initialize();
	IMG_AddInstrumentFunction(loadImage, NULL);
}

static void
onSyscallEnter(THREADID tid, CONTEXT* ctx, SYSCALL_STANDARD std, VOID* v) {
  //从g_thread_context_reg中取出了当前的线程上下文
  ThreadContext* thread_ctx = reinterpret_cast<ThreadContext*>(
      PIN_GetContextReg(ctx, g_thread_context_reg));
  //调用其onSyscallEnter，传入：当前上下文和系统调用类型
  thread_ctx->onSyscallEnter(ctx, std);
}

static void
onSyscallExit(THREADID tid, CONTEXT* ctx, SYSCALL_STANDARD std, VOID* v) {
  //从g_thread_context_reg中取出了当前的线程上下文
  ThreadContext* thread_ctx = reinterpret_cast<ThreadContext*>(
      PIN_GetContextReg(ctx, g_thread_context_reg));
  //调用其onSyscallExit，传入：当前上下文和系统调用类型
  thread_ctx->onSyscallExit(ctx, std);
  //调用clearExprFromReg，传入了一个寄存器类型（可能是AL/AX/EAX/RAX）。
  thread_ctx->clearExprFromReg(getAx(sizeof(ADDRINT)));
}

void initializeQsym() {
  //初始化线程上下文:在
  initializeThreadContext();
  //初始化内存->根据地址空间申请了对应数量的expref内存
  initializeMemory();

	//主要的四个pin api
  //在系统调用前执行onSyscallEnter
	PIN_AddSyscallEntryFunction(onSyscallEnter, NULL);
  //在系统调用后执行onSyscallExit
	PIN_AddSyscallExitFunction(onSyscallExit, NULL);

  //Pin calls this function every time a new basic block is encountered
  //每当出现新的基本块时会调用(***主要逻辑***)
	TRACE_AddInstrumentFunction(analyzeTrace, NULL);
	
  //注册一个全局错误处理程序
  PIN_AddInternalExceptionHandler(exceptionHandler, NULL);
}

} // namespace
