# 原版布尔位机器：全部操作码与任意有限步的 Lean 内核语义等价

**2026-10-29；Ubuntu 24.04；Lean 4.34.1；上游 OpenAI/math 固定于 `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`。**

## 核心结论

对原始 `BitProgram.Instr r s l` **全部 12 类操作码**、任意有限寄存器数 `r`、栈数 `s`、程序位置数 `l`、任意合法 `Cfg r s l` 状态，Lean 内核检查通过：

```lean
theorem runOne_exact {r s l : Nat}
    (instr : Instr r s l) (cfg : Cfg r s l) :
    runOne instr (copyConfig cfg) =
      copyConfig (execInstr instr cfg)
```

这里的 `runOne` 是此前 800 万源位指令实验所使用的紧凑解释器的**单步函数**，`execInstr` 来自没有修改的 OpenAI 上游源码，`copyConfig` 将原版寄存器与栈函数转为紧凑布尔数组。证明通过通用 `Array.ofFn`／`Function.update` 引理及指令构造子归纳，不是 536 个样例的穷举，也没有替代计算结果。

## 任意有限步轨迹连接

独立定义未停机时执行、停机后保持状态的两种单步函数 `sourceStep` 与 `compactStep`；证明：

```lean
theorem all_fuel_exact {r s l : Nat}
    (p : Program r s l) (n : Nat) (c : Cfg r s l) :
    compactFuel p n (copyConfig c) =
      copyConfig (sourceFuel p n c)
```

其中 `n` 是**任意自然数**；证明使用 `runOne_exact` 加自然数归纳，没有直接展开并完成数百万步证明对象。

此外，`bitStep_exact` 对接上游 `BitProgram.step` 的 `Option` 执行语义，`sourceArray_is_ofFn` 和 `direct_table_fuel_exact` 对接原始实验代码使用的 `(List.finRange l).map p.code |>.toArray` 指令表和直接取码执行。原版停机状态不会被伪装成继续执行。

## 精确特化到 OpenAI 原版 afterCode

`NativeAfterCodeDirectCertificate.lean` 直接引用以前 800 万步实验里的源程序：

```lean
abbrev Original := NativeFinishOriginalDirect.source
```

其中 `source` 在原模块中定义为 **`StructuredCalls.compiled NativeLeafPreparation.afterCode 784 788`**，没有独立算法或预测答案。

- `original_array_exact`：该实验使用的整张原版静态取码数组就是 `Array.ofFn Original.code`，不只是之前 119/119 的运行时比较。
- `afterCode_direct_fuel_exact`：对原版 40×896 状态和**任意有限步数**，直接取码执行器与原版 `BitProgram.execInstr` 定义的源级演化一致。
- `afterCode_one_step_exact`：直接对接原版 `BitProgram.step`。

以上均在 Lean 4.34.1 编译通过；`#print axioms` 显示依赖仅 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。共对 **8 个主要定理**保留了原始公理审计输出。

## 复现实验及证据

主要源码：

- [`NativeCompactInterpreterProof.lean`](../execution-prototype/native-aftercode-original-20261029/NativeCompactInterpreterProof.lean)
- [`NativeDirectTraceProof.lean`](../execution-prototype/native-aftercode-original-20261029/NativeDirectTraceProof.lean)
- [`NativeAfterCodeDirectCertificate.lean`](../execution-prototype/native-aftercode-original-20261029/NativeAfterCodeDirectCertificate.lean)

已装好上游与先前模块依赖的 Ubuntu：

```bash
cd ~/3satlocalverify/execution-prototype/native-aftercode-original-20261029
./check_primitive_kernel.sh
```

脚本检查上游 Git pin，编译真实 Lean 模块，保存独立日志，并核对 8 个内核定理公理依赖。原始输出 `kernel-axioms-*.raw.txt`、`primitive-kernel-results.json`、`validate_primitive_kernel_archive.py` 用于离线证据一致性检查；CI **不冒充重跑大型 Lean 上游工程**。

## 未关闭的科学证明缺口

1. **原版整套 `NativeCodeAssembly.command` 与独立连接器的全局标签对应证明仍未完成。** 已证明的直接取码等价对任意原版 `Program` 成立，但不能偷换成“独立连接器生成的代码与上游原版完全相同”。
2. **`runInstrumented` 的统计循环尚未形式化证明与已认证的 `directTableFuel` 同步。** `runInstrumented` 调用的是已经证明的 `runOne`，但循环边界、PC 查询、统计和峰值计算还要做单独证明。此前 800 万步的步骤、资源计数仍是**已复现的实测值**，不是此处内核定理输出的资源上界。
3. **完整 `afterCode` 未停机，完整高查询 `HighQueryProgram` 未执行。** 尚无从真实非空 CNF 到完整 SAT/#SAT 的原版端到端运行或证明。
4. **论文 TM2 实际资源和通用 `2^{o(n)}` 优势没有因此获证。** 对有限程序语义的数学等价并不自动给出论文复杂度上界，尤其不能免除预计算、程序表与真实访问成本。

结论：**原版位机器执行器的“所有操作码 + 所有有限步数”证明关卡取得实质突破，但十关计划中的完整第 1 关仍待关闭。**
