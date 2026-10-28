# 进一步复现：OpenAI 稀疏分支 + 已证明正确的 Moments 计数叶节点

实验位置：`~/eth-lean-check-20261027/execution-prototype/`，于 2026-10-28 在 Ubuntu 24.04.5 / Lean 4.34.1 上完成。OpenAI 原始源码位于 `../openai-math/lean/`，提交 `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`，**没有修改原始仓库**。

## 实验目标与成果

以前已经通过官方 Comparator，但其 `NativeLeafProgram` / `FiniteFallback` 等非构造性定义尚不能直接变成实用 SAT 求解器。本阶段尝试以可执行且可证明的 **Moments 算术叶节点**代替原版 `SparseCountProgram.step` 的形式化 `SAT.count` 语义叶节点。

新建 `MomentsSAT.lean`，直接调用 OpenAI 仓库里的三个可计算代码：

1. `SqrtLog.WalshExistence.tuples`：生成所有布尔赋值（注意这里只用了其中的 **有限元组枚举器**，还没有运行完整谱算法）；
2. `SqrtLog.MomentsAlgorithm.run`：实际对每个赋值下每个子句的真假指示数取乘积，再求和；
3. `SqrtLogSpace.DisjointReuse.SparsePriority.select` 以及原版 `DisjointBranch.childA/childB`：根据公共核心分裂公式，并保持原版深度优先遍历的 pending/total 状态。

此定义的输出确实是精确 #SAT；但 **新叶节点明确枚举 (2^n) 个赋值，所以不是论文所宣称的次指数程序**。它是将真实源码的两个计算模块合并的过渡版本，目的在于验证运行链路。

## Lean 通用定理（实际编译验证）

在 `MomentsSAT.lean` 中，Lean 已证明：

```lean
theorem countMoments_correct {n : Nat} (F : CNF (Fin n)) :
  countMoments F = SAT.count F

theorem sparseMomentsStep_eq_source {n : Nat} (M : Nat)
  (s : SparseCountProgram.State n) :
  sparseMomentsStep M s = SparseCountProgram.step M s

theorem sparseMomentsRun_eq_source {n : Nat} (M t : Nat)
  (s : SparseCountProgram.State n) :
  sparseMomentsRun M t s = SparseCountProgram.run M t s

theorem sparseMomentsRun_exact {n : Nat} (M t : Nat)
  (F : CNF (Fin n))
  (hfinished : (sparseMomentsRun M t (SparseCountProgram.initial F)).pending = []) :
  (sparseMomentsRun M t (SparseCountProgram.initial F)).total = SAT.count F

theorem momentsCost_exact {n : Nat} (F : CNF (Fin n)) :
  momentsCost F = (2 ^ n) * (3 * F.card + 2)
```

其中 `countMoments_correct` 的证明包含对 `WalshExistence.tuples` 无重复、全覆盖的证明，且对每一个赋值，`MomentsAlgorithm.run` 的子句真假乘积等于 `CNF.eval`。`sparseMomentsRun_exact` 利用 OpenAI 原有的不变量定理，而不是单纯通过有限样例猜想。

**公理检查**：`#print axioms` 对 `countMoments_correct`、`sparseMomentsRun_exact`、`momentsCost_exact` 三条定理均只显示 `propext`、`Classical.choice`、`Quot.sound`。此次是直接用 Lean 类型检查/内核接受新证明；尚未给自己编写的文件另配 Comparator 挑战配置。

## 实际执行

- `MomentsSparseDimacs.lean` 读取正常 DIMACS CNF，调用 `Prototype.sparseMomentsStep`，并以原版 `SAT.count` 交叉核对小公式；为避免指数消耗，限制最多 12 个变量，`run_moments.sh` 对每次程序调用有 90 秒限制。
- `python3 regression_moments.py`：**68/68** 个小 CNF 全部通过，并且相较于原版 Lean `SparseCountProgram.step`，**总步数、分支数、叶节点数、最大 pending 深度、精确计数全部相同**；这些用例累计 64 次真实分支。
- 10 变量 45 子句“两两正文字公式”：计数 **11**，8 次分支、9 个 Moments 叶节点，**291,840** 次在 Lean 中有明确定义并验证计数公式的算术操作，Lean 内部计算约 1.3 秒，完整 Lean 进程约 5.9 秒。
- 12 变量 66 子句同类公式：计数 **13**，10 次分支、11 个 Moments 叶节点，**1,699,840** 次计数模型中的算术操作；已通过压力测试。首次修订后的整进程实测约 22.8 秒，约 7.4 GiB RSS；后续重测请使用最新内部计时。

这些“两两正文字公式”有解析解 (n+1)，因为至多一个变量可以为假。这是结构化容易算的例子，并不能说明一般 k-SAT 已加速。

计时 `ms` 位于真正求值得到 `.ok (answer, stats)` **之后**、原版 `SAT.count` 对照 **之前**，不再把惰性求值时间误记为零。Lean 单次进程的 Mathlib 加载时间、约 7 GiB 的缓存驻留内存应与单实例算法资源分开分析。

## 仍然存在的关键缺口

1. 原版 `SqrtLogSpace/NativeLeafProgram.lean` 中的完整有限机器构造仍位于 `noncomputable section`；本阶段没有成功把它直接提取为普通机器代码。
2. `SqrtLogSpace/FiniteFallback.lean` 泛型有限查表及 `NativeEntry` 使用非构造性定义和理论截止阈值；真正抽取需要显式可计算的 cutoff / 具体小输入分支。
3. 这个桥接版本使用原版 Moments **算术循环**，没有实现论文复杂的 Walsh/CRT 插值与叶节点稀疏查询协议。当前的精确成本公式包含 (2^n)，证明了它仍是指数算法。
4. 后续要切换到论文级叶节点，需要给出对应状态输入/输出的计算型实现和正确性引理，再替换 `countMoments` 并在 Lean 里证明它等于 `SAT.count`，最终核对时间与空间；其性能优势目前完全没有被本实验验证。

## 复现命令

```bash
cd ~/eth-lean-check-20261027/execution-prototype
./run_moments_all.sh              # 编译 + 公理 + 68 回归 + n10
./run_moments_all.sh --stress     # 额外运行 n12 压力样例
./run_moments.sh fixtures/shared-core.cnf
```

生成输出：`moments-sat-compile.log`、`moments-axioms.log`、`regression-moments-summary.json`、`regression-moments.stdout.log`、`moments-n10-timed.log`、`moments-n12-timed.log`。详细早期验证见 `EXECUTION_REPORT.md` 和 `../REPRODUCTION_REPORT.md`。
