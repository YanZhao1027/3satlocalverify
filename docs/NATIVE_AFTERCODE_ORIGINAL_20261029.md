# 原版 OpenAI afterCode：119/119 操作码与 800 万位指令核对

**实验时间：2026-10-29；Ubuntu 24.04；Lean 4.34.1；上游 OpenAI/math 固定提交 `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`。**

**证据边界：** 本轮只核验上游 `NativeLeafPreparation.afterCode` 的完整静态操作码表，以及一个真实非空 CNF 的前 800 万条源位指令。该程序**未停机**，后面的 `HighQueryProgram` 未运行，也没有证明通用次指数 #SAT 或 ETH 错误。

## 1. 本轮新增验证

原始输入来自之前的物理 40 寄存器／896 栈实验：3 变量，1 个非空子句 `x₀`，完成原始参数计算、图／局部代码搜索和保存了 13 位的行序列化结果。参见 [上一期报告](NATIVE_CODE_PARAMETERS_SEARCHES_20261029.md)。

本次直接调用原版 `StructuredCalls.compiled NativeLeafPreparation.afterCode 784 788`，通过上游 `Program.code` 构建全部 **119 个操作码**。原版入口为 1，119 个位置逐项与本地 `FastLinearize.instructionArray` 一致（119/119）。这是一项输入无关的、**全表运行时检查**。

**不是 Lean 内核定理：** 尝试直接用 `by decide` 在 Lean 内核中证明整个 119 位置等价时，触及 200 万心跳上限，没有形成定理。仍需结构归纳等更高效的形式化证明。

## 2. 800 万条原版位指令

从真实已序列化物理状态运行，保留原始 PC 和全部布尔栈状态，每 100 万条源指令继续执行而非重启或预填结果。

| 累计真实位指令 | 栈 778 候选编码位数 | 峰值已占用数据位 | 是否停机 |
|---:|---:|---:|---|
| 1,000,000 | 17,614 | 17,744 | 否 |
| 2,000,000 | 35,238 | 35,368 | 否 |
| 3,000,000 | 52,858 | 52,988 | 否 |
| 4,000,000 | 70,478 | 70,608 | 否 |
| 5,000,000 | 88,098 | 88,228 | 否 |
| 6,000,000 | 105,722 | 105,852 | 否 |
| 7,000,000 | 123,342 | 123,472 | 否 |
| **8,000,000** | **140,962** | **141,092** | **否** |

源级 `HashGreedyProgram.Initialize.zeroWord` 规定的目标编码长度为 **5,120,003 位**（距离深度 1,280,000、模数位宽 2）。已生成约 **2.75%** 的目标位数，**不是整套算法完成百分比**。

8 百万步累计实测操作码：条件分支 2,114,560，`pop` 1,973,593，`push` 1,938,340，位逻辑 1,550,609，`set` 211,443，`goto` 105,735，`peek` 105,720；`copy` 和 `halt` 为 0。各种操作码总和严格等于 8,000,000。

机器墙钟耗时 44.34 秒，进程峰值 RSS 8,131,940 KiB（约 7.75 GiB）。Linux RSS 包含 Lean 运行时、上游依赖、模拟器、代码和其他缓存；**不是原始图灵机空间复杂度**。141,092 位也只是实际栈数据占用，不含内存管理、物理磁带、静态代码和寻址代价。不能将短前缀线性外推为完整耗时。

## 3. 原版单步语义差分（536/536）

为审核紧凑执行器 `CompactNative40.runOne`，以原版 `BitProgram.execInstr` 为参照：

- 原版 `afterCode` 的全部 **119 个操作码**，每个放入 **4 种**不同寄存器／栈状态；
- 额外 **15 个**合成指令，覆盖 `halt/goto/set/copy/not/and/or/xor/branch/push/peek/pop`、寄存器重叠、空栈与非空栈；
- 总计 **(119+15)×4=536** 例；逐例比较 PC、40 个寄存器和 **全部 896 栈**，均一致。

**有限差分测试不是全状态的语义等价证明，也不是 800 万步均由两个执行器锁步复核。** 它强化了对实际使用解释器的信心，但没有填平内核级解释器正确性证明缺口。

## 4. 复现与归档

源码及证据在 [`execution-prototype/native-aftercode-original-20261029/`](../execution-prototype/native-aftercode-original-20261029/)：

- `NativeFinishOriginalDirect.lean`：直接以原始编译表执行、逐位置核对并统计各类真实操作码；
- `NativeFinishStepSemanticAudit.lean`：536 例全寄存器／全栈单步差分；
- `aftercode-direct-original-8m-20261029.raw.txt`：原始长跑日志；
- `step-semantic-audit-20261029.raw.txt`：语义差分日志；
- `original-aftercode-results.json`：由原始日志重新生成的结构化数据；
- `validate_original_aftercode.py` 与 `verify_replay.py`：离线原始日志核对与新运行的确定性检查点核对；
- `check_original_aftercode.sh`：完整 Ubuntu 复现实验。

原实验 Ubuntu 上的复现命令：

    cd ~/3satlocalverify/execution-prototype/native-aftercode-original-20261029
    ./check_original_aftercode.sh

脚本核对上游固定提交、使用已构建的前置 Lean 依赖、为每次重跑分配新的日志目录，在真实执行与差分测试失败时立即退出。云端 CI 只执行**离线归档一致性检查**，不冒充已经重跑耗资源的 Lean 程序。

## 5. 下一个验收目标

1. 用结构归纳证明原版编译器与直接取码机制的全表一致，及紧凑执行器在合法状态上的单步语义对应，替代资源昂贵的整表 `decide`。
2. 定量分离循环计数器更新、编码位生成、栈复制和分支的原始位成本，所有优化必须保留源语义与真实指令成本。
3. 安全有界地完成原版整个 `afterCode` 的实际停机和完整物理状态核对，然后继续 `NativeLeafPreparation.command` 与未替换的 `HighQueryProgram`。
4. 用匹配任务的完整精确 #SAT 基线比较真正非特制输入，并计入固定程序、预处理和数据搬运。

**未完成完整 SAT/#SAT，未证明 ETH 错误，未证明通用 `2^{o(n)}` 加速。**
