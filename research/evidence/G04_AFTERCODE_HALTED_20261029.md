# G04：原版 afterCode 完整停机证据（2026-10-29）

**来源：GitHub Draft PR #3**（本卡是独立审阅的证据索引，不表示该 PR 已合并）。

- 原版源码固定为 OpenAI/math `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`。
- PR #3 实验提交（固定 SHA）：`8323964865602a50b772ecb82b42d5a0d6c14e16`。
- 原版 `StructuredCalls.compiled NativeLeafPreparation.afterCode 784 788` 在真实三变量、一个非空子句 `x₀` 的前置物理状态上执行，**290,560,512 条原版源布尔位指令后自然 HALT**，PC 为 `none`。
- 栈 778 生成 **5,120,003** 位编码零候选，恰与上游规格一致；**全部 896 个栈**与经 Lean 内核等价定理支持的缓存版 `NativeLeafPreparation.finishedWords` 参考运行时逐项一致；序列化的 13 位行数据保留。
- 最大已占用栈数据 **5,120,133 位**；进程墙钟时间 **258.35 秒**，峰值 RSS **8,265,020 KiB**。前者是抽象栈内容，不是完整 TM2 物理空间；后两者是 Lean 宿主性能，不是论文渐近复杂度。
- 原始 59 个检查点和各类操作码计数合计 **290,560,512**；宿主性能优化缓存长度，没有跳过原版操作码。宿主外层计量循环本身**还没有通用 Lean 语义等价定理**。
- 2026-10-29 Ubuntu `python3 validate_full_aftercode.py`：`ORIGINAL_AFTERCODE_COMPLETE_OFFLINE_ARCHIVE_PASS (not full SAT/ETH)`；这是原始日志与 JSON 的离线一致性复核，不能冒充这一次对 2.9 亿条指令的重新执行。

可审阅的固定上游实验文件：

- [研究报告](https://github.com/YanZhao1027/3satlocalverify/blob/8323964865602a50b772ecb82b42d5a0d6c14e16/docs/NATIVE_COMPACT_KERNEL_AND_AFTERCODE_COMPLETE_20261029.md)
- [完整机器可读结果与检查点](https://github.com/YanZhao1027/3satlocalverify/blob/8323964865602a50b772ecb82b42d5a0d6c14e16/execution-prototype/native-aftercode-original-20261029/aftercode-original-complete-results.json)
- [原始执行日志](https://github.com/YanZhao1027/3satlocalverify/blob/8323964865602a50b772ecb82b42d5a0d6c14e16/execution-prototype/native-aftercode-original-20261029/aftercode-original-complete.raw.txt)
- [离线结果核验脚本](https://github.com/YanZhao1027/3satlocalverify/blob/8323964865602a50b772ecb82b42d5a0d6c14e16/execution-prototype/native-aftercode-original-20261029/validate_full_aftercode.py)
- [完整带硬上限复现脚本](https://github.com/YanZhao1027/3satlocalverify/blob/8323964865602a50b772ecb82b42d5a0d6c14e16/execution-prototype/native-aftercode-original-20261029/run_complete_native_aftercode.sh)
- [Draft PR #3](https://github.com/YanZhao1027/3satlocalverify/pull/3)

## 科学解释及关卡判定

**G04 提升为 `sample_verified`（指定样例通过）**，并非 `passed`：这份固定样例的 `serialize` 加 `afterCode` 完整收尾确已实测，但尚无第二份非退化 `r > 0` 输入及全输入覆盖。

**G05 仍为 `open`**：原版 `NativeLeafPreparation.command` 整张指令表有 12,539 个静态位置、入口 3；此前整表构造试验 100 秒限时后退出码 124，**没有得到完整单程序一次执行的停机记录**。已逐段运行和状态校验不能冒充原版完整命令一次运行。

**G01 仍为 `partial`**：直接取原版代码执行与独立全局连接器等价是不同命题，后者尚未证明；带计量运行器的全部循环语义也需形式化。
**G08、G09 仍为 `partial`**：不能从这个小样例推断没有高查询 oracle/预制表，更不能推断论文 TM2 资源上界。

**未运行完整原版高查询 SAT/#SAT；没有证明通用次指数优势，更没有证明 ETH 错误。**
