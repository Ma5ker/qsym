#include <set>
#include <byteswap.h>
#include "solver.h"

namespace qsym {

namespace {

const uint64_t kUsToS = 1000000;
const int kSessionIdLength = 32;
const unsigned kSolverTimeout = 10000; // 10 seconds

std::string toString6digit(INT32 val) {
  char buf[6 + 1]; // ndigit + 1
  snprintf(buf, 7, "%06d", val);
  buf[6] = '\0';
  return std::string(buf);
}

uint64_t getTimeStamp() {
  struct timeval tv;
  gettimeofday(&tv, NULL);
  return tv.tv_sec * kUsToS + tv.tv_usec;
}

void parseConstSym(ExprRef e, Kind &op, ExprRef& expr_sym, ExprRef& expr_const) {
  for (INT32 i = 0; i < 2; i++) {
    expr_sym = e->getChild(i);
    expr_const = e->getChild(1 - i);
    if (!isConstant(expr_sym)
        && isConstant(expr_const)) {
      op = i == 0 ? e->kind() : swapKind(e->kind());
      return;
    }
  }
  UNREACHABLE();
}

void getCanonicalExpr(ExprRef e,
    ExprRef* canonical,
    llvm::APInt* adjustment=NULL) {
  ExprRef first = NULL;
  ExprRef second = NULL;
  // e == Const + Sym --> canonical == Sym
  switch (e->kind()) {
    // TODO: handle Sub
    case Add:
      first = e->getFirstChild();
      second = e->getSecondChild();
      if (isConstant(first)) {
        *canonical = second;
        if (adjustment != NULL)
          *adjustment =
            static_pointer_cast<ConstantExpr>(first)->value();
        return;
      case Sub:
        // C_0 - Sym
        first = e->getFirstChild();
        second = e->getSecondChild();
        // XXX: need to handle reference count
        if (isConstant(first)) {
          *canonical = g_expr_builder->createNeg(second);
          if (adjustment != NULL)
            *adjustment = static_pointer_cast<ConstantExpr>(first)->value();
          return;
        }
      }
    default:
      break;
  }
  if (adjustment != NULL)
    *adjustment = llvm::APInt(e->bits(), 0);
  *canonical = e;
}

inline bool isEqual(ExprRef e, bool taken) {
  return (e->kind() == Equal && taken) ||
    (e->kind() == Distinct && !taken);
}

} // namespace

Solver::Solver(
    const std::string input_file,
    const std::string out_dir,
    const std::string bitmap)
  : input_file_(input_file)
  , inputs_()
  , out_dir_(out_dir)
  , context_(g_z3_context)
  , solver_(z3::solver(context_, "QF_BV"))
  , num_generated_(0)
  , trace_(bitmap)
  , last_interested_(false)
  , syncing_(false)
  , start_time_(getTimeStamp())
  , solving_time_(0)
  , last_pc_(0)
  , dep_forest_()
{
  // Set timeout for solver
  z3::params p(context_);
  p.set(":timeout", kSolverTimeout);
  solver_.set(p);

  checkOutDir();
  readInput();//从文件读入输入
}

void Solver::push() {
  solver_.push();
}

void Solver::reset() {
  solver_.reset();
}

void Solver::pop() {
  solver_.pop();
}

void Solver::add(z3::expr expr) {
  if (!expr.is_const())
    solver_.add(expr.simplify());
}

//检查是否有解   或者可以叫 求解过程
z3::check_result Solver::check() {
  uint64_t before = getTimeStamp();
  z3::check_result res;
  LOG_STAT(
      "SMT: { \"solving_time\": " + decstr(solving_time_) + ", "
      + "\"total_time\": " + decstr(before - start_time_) + " }\n");
  // LOG_DEBUG("Constraints: " + solver_.to_smt2() + "\n");
  try {
    res = solver_.check();
  }
  catch(z3::exception e) {
    // https://github.com/Z3Prover/z3/issues/419
    // timeout can cause exception
    res = z3::unknown;
  }
  uint64_t cur = getTimeStamp();
  uint64_t elapsed = cur - before;
  solving_time_ += elapsed;
  LOG_STAT("SMT: { \"solving_time\": " + decstr(solving_time_) + " }\n");
  return res;
}

//有解保存 返回true
bool Solver::checkAndSave(const std::string& postfix) {
  //有解则保存
  if (check() == z3::sat) {
    saveValues(postfix);
    return true;
  }
  //否则输出无解调试信息 并返回false
  else {
    LOG_DEBUG("unsat\n");
    return false;
  }
}
//called from instrumentJcc
void Solver::addJcc(ExprRef e, bool taken, ADDRINT pc) {
  // Save the last instruction pointer for debugging
  last_pc_ = pc;

  if (e->isConcrete())
    return;

  // if e == Bool(true), then ignore
  //如果这个jcc的跳转条件恒为真 就忽略
  if (e->kind() == Bool) {
    assert(!(castAs<BoolExpr>(e)->value()  ^ taken));
    return;
  }

  assert(isRelational(e.get()));

  // check duplication before really solving something,
  // some can be handled by range based constraint solving
  bool is_interesting;
  if (pc == 0) {
    // If addJcc() is called by special case, then rely on last_interested_
    is_interesting = last_interested_;
  }
  else
    is_interesting = isInterestingJcc(e, taken, pc);

  //
  if (is_interesting)
    //对其另一分支求解
    negatePath(e, taken);
  addConstraint(e, taken, is_interesting);
}

void Solver::addAddr(ExprRef e, ADDRINT addr) {
  llvm::APInt v(e->bits(), addr);
  addAddr(e, v);
}

void Solver::addAddr(ExprRef e, llvm::APInt addr) {
  //如果这个表达式是具体化的话，不作处理
  if (e->isConcrete())
    return;
  //判断是否是有趣测试用例  应该是对重复执行的修剪
  if (last_interested_) {
    reset();
    // TODO: add optimize in z3
    syncConstraints(e);
    if (check() != z3::sat)
      return;
    z3::expr &z3_expr = e->toZ3Expr();

    // TODO: add unbound case
    //获取边界值
    z3::expr min_expr = getMinValue(z3_expr);//z3_expr的最小值(不包括等于)
    z3::expr max_expr = getMaxValue(z3_expr);//z3_expr的最大值(不包括等于)
    solveOne(z3_expr == min_expr);//对上面遗漏的边界值进行求解
    solveOne(z3_expr == max_expr);
  }
  //将约束条件添加进节点
  addValue(e, addr);
}

void Solver::addValue(ExprRef e, ADDRINT val) {
  llvm::APInt v(e->bits(), val);
  addValue(e, v);
}

//添加一个值约束
void Solver::addValue(ExprRef e, llvm::APInt val) {
  if (e->isConcrete())
    return;

#ifdef CONFIG_TRACE
  trace_addValue(e, val);
#endif

  ExprRef expr_val = g_expr_builder->createConstant(val, e->bits());
  ExprRef expr_concrete = g_expr_builder->createBinaryExpr(Equal, e, expr_val);//构建Equal(e==val)的约束表达式

  addConstraint(expr_concrete, true, false);
}
//求解：先尝试结合前面的所有约束一起求解；失败的话就启动optimistic solving，只求解最后一次的约束；最后将此次的约束加入条件池方便syncConstraints(e)去同步
void Solver::solveAll(ExprRef e, llvm::APInt val) {
  //这里的last_interested_用来判定当前分支是否是interesting的
  if (last_interested_) {//如果last_interested_被置为true 开始进行求解
    std::string postfix = "";
    ExprRef expr_val = g_expr_builder->createConstant(val, e->bits());//val的表达式
    ExprRef expr_concrete = g_expr_builder->createBinaryExpr(Equal, e, expr_val);//构建Equal(e==val)的约束表达式

    reset();//重置solver
    //author issue: 
    //对于optimistic solving，只求解最后一次的约束；
    //对于普通的求解  会通过syncConstraints(e)同步所有约束
    syncConstraints(e);
    //将当前约束的相反约束加入求解器
    addToSolver(expr_concrete, false);
    //检查无解  启用optimistic 求解，得到的case会添加后缀"optimistic" 
    if (check() != z3::sat) {
      // Optimistic solving ，只放入当前分支约束的相反条件
      reset();
      addToSolver(expr_concrete, false);
      postfix = "optimistic";
    }
    //获得传入ExprRef的z3Expr
    z3::expr z3_expr = e->toZ3Expr();
    while(true) {
      //循环尝试求解。如果求解失败则退出循环
      if (!checkAndSave(postfix))
        break;
      //求解成功后
      //获取模型中一个可能的z3_expr值
      z3::expr value = getPossibleValue(z3_expr);
      //循环求解其他的可能值？
      add(value != z3_expr);
    }
  }
  addValue(e, val);//添加进约束，以便后续求解使用(也就是上面说的normal solving)
}

UINT8 Solver::getInput(ADDRINT index) {
  assert(index < inputs_.size());
  return inputs_[index];
}

void Solver::checkOutDir() {
  // skip if there is no out_dir
  if (out_dir_.empty()) {
    LOG_INFO("Since output directory is not set, use stdout\n");
    return;
  }

  struct stat info;
  if (stat(out_dir_.c_str(), &info) != 0
      || !(info.st_mode & S_IFDIR)) {
    LOG_FATAL("No such directory\n");
    exit(-1);
  }
}

void Solver::readInput() {
  std::ifstream ifs (input_file_, std::ifstream::in | std::ifstream::binary);
  if (ifs.fail()) {
    LOG_FATAL("Cannot open an input file\n");
    exit(-1);
  }

  char ch;
  while (ifs.get(ch))
    inputs_.push_back((UINT8)ch);
}

std::vector<UINT8> Solver::getConcreteValues() {
  // TODO: change from real input
  z3::model m = solver_.get_model();
  unsigned num_constants = m.num_consts();
  std::vector<UINT8> values = inputs_;
  for (unsigned i = 0; i < num_constants; i++) {
    z3::func_decl decl = m.get_const_decl(i);
    z3::expr e = m.get_const_interp(decl);//
    z3::symbol name = decl.name();//符号名称

    if (name.kind() == Z3_INT_SYMBOL) {
      int value = e.get_numeral_int();//获取值 替换原始输入中的对应部分
      values[name.to_int()] = (UINT8)value;
    }
  }
  return values;
}

//输出结果   postfix为前后缀
void Solver::saveValues(const std::string& postfix) {
  std::vector<UINT8> values = getConcreteValues();

  // If no output directory is specified, then just print it out
  if (out_dir_.empty()) {
    printValues(values);
    return;
  }
  //输出文件名
  std::string fname = out_dir_+ "/" + toString6digit(num_generated_);
  // Add postfix to record where it is genereated
  if (!postfix.empty())
      fname = fname + "-" + postfix;
  ofstream of(fname, std::ofstream::out | std::ofstream::binary);
  LOG_INFO("New testcase: " + fname + "\n");
  if (of.fail())
    LOG_FATAL("Unable to open a file to write results\n");

      // TODO: batch write
      for (unsigned i = 0; i < values.size(); i++) {
        char val = values[i];
        of.write(&val, sizeof(val));
      }

  of.close();
  num_generated_++;
}

void Solver::printValues(const std::vector<UINT8>& values) {
  fprintf(stderr, "[INFO] Values: ");
  for (unsigned i = 0; i < values.size(); i++) {
    fprintf(stderr, "\\x%02X", values[i]);
  }
  fprintf(stderr, "\n");
}

//获取模型中z3_expr的一个值
z3::expr Solver::getPossibleValue(z3::expr& z3_expr) {
  z3::model m = solver_.get_model();
  return m.eval(z3_expr);
}

//通过枚举一个可能值，并循环设置小于约束，不断缩小解的范围找到解的最小值(返回的是一个加入z3_expr<value条件会无解的value)
z3::expr Solver::getMinValue(z3::expr& z3_expr) {
  push();
  z3::expr value(context_);
  while (true) {
    if (checkAndSave()) {//为啥求最小的过程中还要保存求解结果
      value = getPossibleValue(z3_expr);
      //利用添加小于条件，不断缩小z3_expr至一个最小值
      solver_.add(z3::ult(z3_expr, value));//位向量的无符号小于 z3::ult 
    }
    else
      break;
  }
  pop();
  return value;
}
//通过枚举一个可能值，并循环设置大于约束，不断缩小解的范围找到解的最大值(返回的是一个加入z3_expr>value条件会无解的value)
z3::expr Solver::getMaxValue(z3::expr& z3_expr) {
  push();
  z3::expr value(context_);
  while (true) {
    if (checkAndSave()) {//这也是，为啥求解这个过程的所有值全部输出
      value = getPossibleValue(z3_expr);
      solver_.add(z3::ugt(z3_expr, value));
    }
    else
      break;
  }
  pop();
  return value;
}
//将条件表达式添加进solver，taken表示是否取反
void Solver::addToSolver(ExprRef e, bool taken) {
  e->simplify();
  if (!taken)
    e = g_expr_builder->createLNot(e);
  add(e->toZ3Expr());
}
//同步约束
void Solver::syncConstraints(ExprRef e) {
  std::set<std::shared_ptr<DependencyTree<Expr>>> forest;
  DependencySet* deps = e->getDependencies();

  for (const size_t& index : *deps)
    forest.insert(dep_forest_.find(index));

  for (std::shared_ptr<DependencyTree<Expr>> tree : forest) {
    std::vector<std::shared_ptr<Expr>> nodes = tree->getNodes();
    for (std::shared_ptr<Expr> node : nodes) {
      if (isRelational(node.get()))
        addToSolver(node, true);
      else {
        // Process range-based constraints
        bool valid = false;
        for (INT32 i = 0; i < 2; i++) {
          ExprRef expr_range = getRangeConstraint(node, i);
          if (expr_range != NULL) {
            addToSolver(expr_range, true);
            valid = true;
          }
        }

        // One of range expressions should be non-NULL
        if (!valid)
          LOG_INFO(std::string(__func__) + ": Incorrect constraints are inserted\n");
      }
    }
  }

  checkFeasible();
}

void Solver::addConstraint(ExprRef e, bool taken, bool is_interesting) {
  if (auto NE = castAs<LNotExpr>(e)) {
    addConstraint(NE->expr(), !taken, is_interesting);
    return;
  }
  if (!addRangeConstraint(e, taken))
    addNormalConstraint(e, taken);
}

void Solver::addConstraint(ExprRef e) {
  // If e is true, then just skip
  //如果恒为true  跳过
  if (e->kind() == Bool) {
    QSYM_ASSERT(castAs<BoolExpr>(e)->value());
    return;
  }
  //如果是具体值表达式 跳过
  if (e->isConcrete())
    return;
  //添加约束
  dep_forest_.addNode(e);
}

bool Solver::addRangeConstraint(ExprRef e, bool taken) {
  if (!isConstSym(e))
    return false;

  Kind kind = Invalid;
  ExprRef expr_sym, expr_const;
  parseConstSym(e, kind, expr_sym, expr_const);
  ExprRef canonical = NULL;
  llvm::APInt adjustment;
  getCanonicalExpr(expr_sym, &canonical, &adjustment);
  llvm::APInt value = static_pointer_cast<ConstantExpr>(expr_const)->value();

  if (!taken)
    kind = negateKind(kind);

  canonical->addConstraint(kind, value,
      adjustment);
  addConstraint(canonical);
  //updated_exprs_.insert(canonical);
  return true;
}

void Solver::addNormalConstraint(ExprRef e, bool taken) {
  if (!taken)
    e = g_expr_builder->createLNot(e);
  addConstraint(e);
}

ExprRef Solver::getRangeConstraint(ExprRef e, bool is_unsigned) {
  Kind lower_kind = is_unsigned ? Uge : Sge;
  Kind upper_kind = is_unsigned ? Ule : Sle;
  RangeSet *rs = e->getRangeSet(is_unsigned);
  if (rs == NULL)
    return NULL;

  ExprRef expr = NULL;
  for (auto i = rs->begin(), end = rs->end();
      i != end; i++) {
    const llvm::APSInt& from = i->From();
    const llvm::APSInt& to = i->To();
    ExprRef bound = NULL;

    if (from == to) {
      // can simplify this case
      ExprRef imm = g_expr_builder->createConstant(from, e->bits());
      bound = g_expr_builder->createEqual(e, imm);
    }
    else
    {
      ExprRef lb_imm = g_expr_builder->createConstant(i->From(), e->bits());
      ExprRef ub_imm = g_expr_builder->createConstant(i->To(), e->bits());
      ExprRef lb = g_expr_builder->createBinaryExpr(lower_kind, e, lb_imm);
      ExprRef ub = g_expr_builder->createBinaryExpr(upper_kind, e, ub_imm);
      bound = g_expr_builder->createLAnd(lb, ub);
    }

    if (expr == NULL)
      expr = bound;
    else
      expr = g_expr_builder->createLOr(expr, bound);
  }

  return expr;
}

//called from addJcc
bool Solver::isInterestingJcc(ExprRef rel_expr, bool taken, ADDRINT pc) {
  bool interesting = trace_.isInterestingBranch(pc, taken);
  // record for other decision
  last_interested_ = interesting;
  return interesting;
}

//求解相反路径
void Solver::negatePath(ExprRef e, bool taken) {
  reset();
  syncConstraints(e);
  addToSolver(e, !taken);
  bool sat = checkAndSave();
  if (!sat) {
    reset();
    // optimistic solving
    addToSolver(e, !taken);
    checkAndSave("optimistic");
  }
}

//加入z3_expr 后尝试求解，之后去掉此z3_expr 
void Solver::solveOne(z3::expr z3_expr) {
  push();//类似栈操作  将当前solver环境保存
  add(z3_expr);//添加一个z3_expr约束
  checkAndSave();//尝试求解
  pop();//之后恢复之前的环境
}

void Solver::checkFeasible() {
#ifdef CONFIG_TRACE
  if (check() == z3::unsat)
    LOG_FATAL("Infeasible constraints: " + solver_.to_smt2() + "\n");
#endif
}

} // namespace qsym
