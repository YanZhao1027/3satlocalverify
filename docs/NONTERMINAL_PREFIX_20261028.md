# 非终止 3-SAT 输入：原版入口执行与紧凑指令实验

**2026-10-28 · Ubuntu 24.04 · Lean 4.34.1 · 原版 OpenAI/math commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`**

## 先用一分钟看懂

试想我们把一道数学题送进一台设计非常复杂的计算机。有三件事要分别确认：

1. **设计图过审：** Lean 可以检查程序的数学性质。这不等于电脑已经跑过完整程序。
2. **确实能读题并准备工作区：** 这次在四道不是空题的 3-SAT 公式上，原版输入分类器和原版工作区加载过程都**实际执行完成**。这是本报告新的证据。
3. **核心计算并展示速度优势：** 还**没有**执行到原版 `HighQueryProgram` 的完整查询与重构，因此还没有验证真正的 #SAT 求解速度，更没有证明通用次指数时间的实际优势。

**简短结论：机器真正打开了门、把题目装进工作区；还没让里面的关键计算引擎解完题。**

## 真实输入和四组实测

所有输入都包含至少一个**非空子句**且不包含空子句，因此不会被 `NativeTerminal` 直接作为“空公式”或“空子句”的简单特例返回。程序源来自原始 `NativeTerminal.readyCommand` 和原始 `Native.loadLeaf`。为保护实验边界，我们把这两个完整真实阶段拼成一个**有限前缀程序**，随后显式停止：**原版的后续高查询分支并未执行，也未替换成伪造答案。**

| 3 变量公式 | 用独立 `SAT.count` 验证的正确 #SAT | 实际前缀位指令（含 HALT） | 总栈数据峰值 | 最大单栈长度 | 真实分类并完成加载 |
| --- | ---: | ---: | ---: | ---: | --- |
| `x₀` | 4 | 3,166 | 52 位 | 17 位 | 是 |
| `x₀ ∧ ¬x₁` | 2 | 3,552 | 92 位 | 37 位 | 是 |
| `x₀ ∧ ¬x₀`（无解但无空子句） | 0 | 3,408 | 76 位 | 29 位 | 是 |
| `(x₀∨x₁) ∧ (¬x₀∨x₂)` | 4 | 4,272 | 172 位 | 77 位 | 是 |

**表中“正确 #SAT”是独立数学校验答案，绝不是执行器输出的计数。** 程序真实输出的是分类标志和拷入叶节点的公式、变量维度及参数。完整原版叶节点仍未返回这些 #SAT 结果。

实测源级指令来自项目独立线性化器把原版 `Cmd` 的有限指令表展开后，使用原版 `BitProgram.Instr` 类型执行得到。后续查询没有纳入这些数字。总栈数据峰值是 1,220 个源级栈中正在存放的布尔位总和的最大值；不同于单栈上界、已访问磁带单元数或 Linux RSS。

## 两类独立核对，不混为一谈

**真正通过 Lean 内核证明（原版语义）：**

- `NonterminalSourceProof.lean`：对 `x₀` 证明物理输入满足原版 `DFSVisit.LeafReady`，且不是终止特例。
- 使用原版 `NativeTerminal.readyCommand_eval` 和 `Native.loadLeaf_eval` 合成一个真实 `StructuredCalls.Eval`，证明完整的公式、维度、参数被送到 ABI 指定的位置。
- `original_nonterminal_compiled_prefix_trace` 通过原版 `StructuredCalls.compiled_halt_trace` 转换成相同前缀的原版位程序轨迹；另有独立 `SAT.count` 定理证明该小实例答案是 4，但不将该答案注入执行。
- `NonterminalAxioms.lean` 公理审计：9 个已检查定理（包括 3 个线性化器指令数量定理）仅依赖 `propext`、`Classical.choice`、`Quot.sound`。证明源码无 `sorry` / `admit` / `native_decide`。
- 独立线性化编译器的指令表**长度保持**定理通过 Lean；这**不是**全程序 opcode 语义等价定理。

**实际执行与对照测试（不是通用证明）：**

- `NativeNonterminalClassifier.lean`：直接调用**原版** `BitProgram.step NativeTerminal.program`，真实执行 248 条源级指令，正确标记“非空、无空子句”；总栈峰值 47 位。
- 独立的 `LinearizedCompiler.lean` 将前缀编成 2,856 个静态标签的紧凑 `BitProgram.Instr` 数组；紧凑解释器记录了四组源级步骤和空间值。
- 首 60 个静态标签的 opcode 与未修改的原版 `program.code` 一一吻合；在真实输入上，**首 100 步的程序计数器、所有 80 个寄存器与全部 1,220 个栈**与原版直接解释完全相同。
- 对 3,166 步的完整已执行前缀，额外独立地在**每一步**重算全部 1,220 个栈的数据占用和最长栈，核对快速统计器为 `true`。
- 先前尝试单进程顺序比较全部 2,856 个静态标签，在 420 秒限制处超时。随后以 160 个标签/任务、6 进程并行试验，首批 6 个任务都在 240 秒超时，已主动取消任务以避免无效占用。**没有全量成功结论。** 分块运行器会把任何超时明确记录为失败，未通过前仍属于开放项。

## 为什么原版解释器慢，这项改进意味着什么

上游 `StructuredCalls.compiled` 用深层嵌套的有限位置类型 `Site` 和双射计算 `program.code label`。对于几千个源代码位置，直接递归解码当前标签的计算开销会很大。我们单独写了一个**线性位置展开器**：在同样的源指令语义下把有限命令表装入数组，使执行时按数字标签直接取下一条 `Instr`。

这显著改善**实验解释器**的成本，解决了此前真实输入前缀的超时问题。**这既不是论文原算法本身的加速，也不构成最快 SAT 求解器的实证。** 独立展开器目前仍须补全全位置 opcode 一致性证据或数学证明；已经通过的核对范围上文逐一列明。

## 离最终目标还缺什么

更接近核心的一个新观察：`PreparationSizeProbe.lean` 对**原版** `NativeLeafPreparation.command` 的指令数量进行直接计算，得到 **12,538 个静态指令位置**；这是**代码体积**，不是该程序已经运行的步骤数。尝试将它直接拼接到完整入口程序后，单次原型编译/求值受 35 秒上限所阻，尚无执行结论。这提示下一阶段需先解决程序的紧凑构造，不能视完整准备程序为免费已执行的服务。

源码依赖追踪发现原版 `NativeLeafProgram` → `HighQueryProgram` → `QueryStreamProgram` → `SignatureTupleComplete.command` → `QueryVisitorProgram.visitor` 的部分声明处于 `noncomputable` 编译障碍链中。已有的逐层探针能定位到此处，但**没有证明每个依赖都是实质不可构造的算法操作**。

下一项真正关键的成就是：在**保持原版查询/计数语义并可验收的实现**中，让这些非空公式的计算继续通过原版高查询、结束并得到精确答案；随后才可能做端到端时间与空间对照。不能把独立校验用的 `SAT.count`、跳过的分支或事前查表结果冒充算法完成的运算。

## 完整复现

环境需自行准备原版 pinned `openai/math` Lean 目录及其 Lake 依赖；执行：

```bash
cd ~/3satlocalverify/execution-prototype/native-leaf-nonterminal-20261028
./check_nonterminal_prefix.sh
```

可定制上游目录：`OPENAI_MATH_LEAN=/path/to/openai-math/lean`。检查器重新编译 Lean 证明、审计公理、运行四组实际有限前缀、独立验证步骤/空间、执行原版与紧凑版的有限差异测试，失败时非零退出。完整静态指令比较**不在快速复现脚本内**，需要时运行 `run_chunked_opcode_diff.py`，其任意超时或错误不会被算作成功。GitHub Actions 仅做离线结果一致性核验，不等于在云端重建庞大的上游 Lean 环境。

项目其他阶段见 [研究现状](RESEARCH_OUTLOOK_20261028.md)、[此前终止路径实测](NATIVE_LEAF_TERMINAL_EXECUTION_20261028.md) 和 [复杂度局限](COMPLEXITY_20261028.md)。
