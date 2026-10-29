# G05：原版完整准备命令的符号取码、任意有限步语义及首标签探针

日期：2026-10-29。上游 OpenAI/math 固定提交：`7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`。

本轮并未宣称完成 G05 所需的**一次真实单程序从公式输入到查询准备状态并停机**；核心障碍仍然是整个源码程序的指令表构造、全标签等价和完整运行。

## 内核定理（已成功编译）

文件 [`NativeFullPreparationDirectCertificate.lean`](../../execution-prototype/native-aftercode-original-20261029/NativeFullPreparationDirectCertificate.lean) 对以下**真正的原版**程序：

```lean
StructuredCalls.compiled NativeLeafPreparation.command 784 788
```

建立了四条 Lean 核验的定理：

- `original_full_code_table_is_source`：原版 `Program.code` 的全部标签经 `finRange/map/toArray` 枚举与 `Array.ofFn` 取码函数相同；
- `every_finite_full_preparation_prefix_exact`：对任意自然数步数、任意合法 40 寄存器／896 栈初态，**已定义的**源位机有限步演化与紧凑直接取码解释器语义相同；
- `every_full_preparation_step_exact`：与上游原版 `BitProgram.step` 单步关系一致；
- `original_full_program_entry`：原版编译程序入口 PC 值为 **3**。

公理审计仅包含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。从通用程序定理代入完整原版程序，并**没有强制生成全部 12,539 条操作码**，因此不等同于全表实际生成成功或整程序执行。原版静态标签数 **12,539** 当前来自上游计算后的运行时记录；直接尝试将全部数量判等变成 `by decide` 的内核定理失败，不能把这个数字写成已内核证明。

## 有界直接原版取码探针

[`NativeFullPreparationLazyProbe.lean`](../../execution-prototype/native-aftercode-original-20261029/NativeFullPreparationLazyProbe.lean) 直接在原版 `Program.code` 上读取跨越开头、中间和末尾的 9 个标签：`0, 3, 4, 5, 3160, 3161, 9000, 12421, 12538`，**没有构造独立线性化整表**。

实际输出：入口 PC 3；PC 3 为其他操作码，PC 4 为条件分支，PC 5 为其他操作码；完成 9 处真实原版 opcode 读取，宿主墙钟耗时 25.55 秒，Lean RSS 峰值 7,998,720 KiB；读码耗时受标签位置和首次预热影响，不能据此线性外推整张表的构造或执行开销。

分类只记录 `halt/goto/branch/other`。这是**九处源码取码示例**，不是编译器全表等价，更不是源位指令执行、停机或资源复杂度证明。

原始审核日志：[四定理公理审计](G05_FULLPREP_CERTIFICATE_AXIOMS_20261029.raw.txt) · [直接取码探针](G05_LAZY_ORIGINAL_OPCODE_20261029.raw.txt)。

## 当前硬障碍与实验设计

原版 `NativeLeafPreparation.command` 有约 12,539 个静态标签；先前试验一次构造完整快速线性化数组，100 秒硬截止时仍未产生表并超时。另一个有界探针证明了若只读取少数原始标签，至少这些指令可以从上游程序函数直接取得；但**把每次取码的宿主成本照搬进数亿步循环并不实际**。因此需要保持严格的代码等价证明，研究结构性分段与缓存取码，而不能跳过源位指令或预制结果。

还欠：(1) 原版完整代码映射与独立连接器全局等价；(2) 可信的高效率原版取码表构造；(3) 原版完整 `NativeLeafPreparation.command` 从真实输入到终态的**一次源级执行**及真实成本。

**G05 仍为 `open`；G01 部分证明，G04 指定样例通过，G06–G10 不因此自动通过。**

## 可复现核验（不会运行完整 G05 到 HALT）

在原始 Ubuntu Lean 环境、固定 OpenAI/math 提交及已编译前置依赖下：

    cd ~/3satlocalverify-ten-gates-board-20261029/execution-prototype/native-aftercode-original-20261029
    ./check_full_preparation_certificate.sh --sample

该脚本先重编译通用位指令的内核证明，再重编译四条完整准备命令的符号定理并严格检查公理依赖；可选 `--sample` 实际读取九个原版标签。脚本检查研究看板与 JSON/RAG 语料一致。测试成功只能记作 **G05_SYMBOLIC_QA_PASS**，绝不能据此登记完整准备命令已运行到 HALT。

注：本项目的独立工作树可能与上面示例目录不同，脚本基于它自己的目录解析仓库路径；不需要移动或覆盖原来的实验记录。
