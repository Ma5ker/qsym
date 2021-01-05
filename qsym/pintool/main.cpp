#include <cstdio>
#include <errno.h>
#include <sys/socket.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <set>

#include "third_party/libdft/syscall_hook.h"
#include "third_party/libdft/api.h"
#include "solver.h"
#include "memory.h"
#include "expr.h"

namespace qsym {
  const int     kExitFailure = -1;
  const char*   kDlibSuffix = ".so";

  z3::context   g_z3_context;
  Memory        g_memory;
  REG           g_thread_context_reg;
  Solver        *g_solver;
  ExprBuilder   *g_expr_builder;
  CallStackManager g_call_stack_manager;
}

#define SYS_SOCKET 1

using namespace qsym;

//添加额外的参数选项  分别对应默认值  名称  用途
//是否stdin输入
static KNOB<size_t> g_opt_stdin(KNOB_MODE_WRITEONCE, "pintool",
    "s", "0", "track stdin");
//是否文件输入
static KNOB<size_t> g_opt_fs(KNOB_MODE_WRITEONCE, "pintool",
    "f", "0", "tracking file name");
//是否网络输入
static KNOB<size_t> g_opt_net(KNOB_MODE_WRITEONCE, "pintool",
    "n", "0", "track net");
//输入文件路径
static KNOB<std::string> g_opt_input(KNOB_MODE_WRITEONCE, "pintool",
    "i", "", "input");
//输出文件路径
static KNOB<string> g_opt_outdir(KNOB_MODE_WRITEONCE, "pintool",
    "o", "", "output directory");
//bitmap 路径
static KNOB<string> g_opt_bitmap(KNOB_MODE_WRITEONCE, "pintool",
    "b", "", "bitmap file");
//似乎是z3的参数
static KNOB<int> g_opt_linearization(KNOB_MODE_WRITEONCE, "pintool",
    "l", "0", "turn on linearization");

namespace {

bool checkOpt() {
  /* 
   * 检查输入类型和输入文件参数
   * 三种输入类型只能存在一种，并且输入文件参数必须给定   
  */
  bool b1 = g_opt_stdin.Value() != 0;
  bool b2 = g_opt_fs.Value() != 0;
  bool b3 = g_opt_net.Value() != 0;

  //输入文件路径
  if (g_opt_input.Value().empty()) {
    LOG_INFO("No input is specified\n");
    return false;
  }

  //三种输入至少有一个
  // one of them should be true
  if (!b1 && !b2 && !b3) {
    LOG_INFO("No option is specified: use stdin\n");
    g_opt_stdin.AddValue("1");
    return true;
  }

  // three of them cannot be true at the same time
  //三种输入只能有一个
  if (b1 && b2 && b3)
    goto multiple_opt;

  // if two of them are true, then false
  // else one of them are true, then true
  if (b1 ^ b2 ^ b3)
    return true;

multiple_opt:
  LOG_INFO("More than one exclusive options are specified\n");
  return false;
}
//初始化z3  -> g_solver
void initializeGlobalContext(
    const std::string input,
    const std::string out_dir,
    const std::string bitmap) {
  g_solver = new Solver(input, out_dir, bitmap);

  if (g_opt_linearization.Value())
    g_expr_builder = PruneExprBuilder::create();
  else
    g_expr_builder = SymbolicExprBuilder::create();
}

} // anonymous namespace

int main(int argc, char** argv) {
  //pin 初始化符号
  PIN_InitSymbols();

  //pin初始化
  if (PIN_Init(argc, argv))
    goto err;

  //检查参数
  if (!checkOpt())
    goto err;

  //fun 1
  //主要hook一些和输入有关的系统调用 应该是用来打污点,  syscall_hook.cpp 
  hookSyscalls(
        g_opt_stdin.Value() != 0,
        g_opt_fs.Value() != 0,
        g_opt_net.Value() != 0,
        g_opt_input.Value());

  //初始化z3的环境
  initializeGlobalContext(
      g_opt_input.Value(),
      g_opt_outdir.Value(),
      g_opt_bitmap.Value());
  //key function in it,   api.cpp
  initializeQsym();
  //pin启动程序
  PIN_StartProgram();

err:
  PIN_ERROR(KNOB_BASE::StringKnobSummary() + "\n");
  return kExitFailure;
}
