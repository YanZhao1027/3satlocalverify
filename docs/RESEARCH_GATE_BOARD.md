# 3satlocalverify：十关研究看板（证据驱动）

**人工复核日期：2026-10-29** · 上游固定提交：`7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`

单一可信源：[结构化清单](../research/ten_gates.json) · [检索卡片 JSONL](../research/gate_cards.jsonl) · [Agent 快速上下文](../research/AGENT_CONTEXT.md) · [人工复核日志](../research/REVIEW_LOG.md) · [方法限制](METHODS_AND_LIMITATIONS.md)

这里的检索卡片是 **RAG-ready 语料，不是已经运行的向量数据库或后台自动监控系统**。

## 总览

**完整验收：0/10**；指定样例通过：2/10；部分证据：4/10；未通过：4/10。 不把局部样例当作通用完成，也不使用误导性的总百分比。

| 关卡 | 项目 | 状态 | 首要缺口 | 优先级 |
|:---:|---|---|---|:---:|
| [G01](#g01) | 原版编译器完全等价验证 | 部分证据，未过关 | 独立全局连接器尚未获得整表等价定理 | P0 |
| [G02](#g02) | 运行代码参数生成 | 指定样例通过，非通用 | 当前实例很小，不足以支持所有输入的性能或通用鲁棒性 | P1 |
| [G03](#g03) | 运行两个代码搜索程序 | 指定样例通过，非通用 | 当前图维数 r=0，搜索可能退化；还没有代表性非平凡图结构的完整回归 | P1 |
| [G04](#g04) | 完成代码序列化与收尾 | 部分证据，未过关 | 完整编码要求 5,120,003 位；afterCode 的完整停机、峰值及末状态没有实测 | P0 |
| [G05](#g05) | 完整运行 NativeLeafPreparation.command | 未通过 | 第 4 关 afterCode 没有完成 | P0 |
| [G06](#g06) | 运行高查询核心 | 未通过 | 完整准备状态尚未形成 | P0 |
| [G07](#g07) | 运行完整 SAT/#SAT 求解器 | 未通过 | 关卡 5、6 尚未通过 | P1 |
| [G08](#g08) | 排除隐藏的不可执行依赖 | 部分证据，未过关 | 尚无完整高查询路径静态与动态调用图清单 | P0 |
| [G09](#g09) | 严格对应论文 TM2 资源模型 | 部分证据，未过关 | 没有全量 TM2 磁带微步/寻址的已证对应 | P0 |
| [G10](#g10) | 验证通用次指数复杂度与性能 | 未通过 | 完整运行路径缺失 | P1 |

## 下一轮工作队列

**两条主要工作线：** G01 的连接器与真实计量执行器的语义闭环，以及 G04 的原版 afterCode 完整执行。 G08 和 G09 是贯穿式审计；G02、G03 的成功样例不替代非退化输入验收。

- **G01 原版编译器完全等价验证**：先给 runInstrumented 构造无计量投影等价定理，再把结构归纳扩展到整套 NativeCodeAssembly 的原版与独立连接器
- **G04 完成代码序列化与收尾**：在硬资源上限内推进 afterCode 的真实执行，分解零候选构造开销；以实际停机与逐状态核对为验收
- **G05 完整运行 NativeLeafPreparation.command**：在关卡 4 停机验证和关卡 1 连接证明之后，执行单程序端到端查询准备并核验全部边界
- **G06 运行高查询核心**：定位 HighQuery 关键路径中的首个不可计算依赖并在不绕过计算的前提下给出可执行且等价的路径
- **G08 排除隐藏的不可执行依赖**：梳理原版高查询及有限回退的调用图，逐个登记可计算性、表大小、生成方式和运行代价
- **G09 严格对应论文 TM2 资源模型**：先形式化 runInstrumented 的源级计量，再验证栈访问与物理 TM2 微步之间的逐类成本对应

## 每关的验收与可追溯证据

<a id="g01"></a>
### G01 · 原版编译器完全等价验证

**状态：部分证据，未过关** · 难度：中高 · 优先级：P0 · 上次复核：2026-10-29

**怎样才算通过**
- 对 OpenAI 原版 NativeCodeAssembly.command / NativeLeafPreparation.command 及独立连接器建立覆盖全部标签与分支跳转的代码相等或轨迹保持定理
- 源码固定，Lean 内核可重编译，公理审计无 sorryAx，且与原版运行轨迹无矛盾

**目前证实的范围**
- 原版 afterCode 的 119 个静态操作码已运行时逐项匹配；原版取码数组已获专用 Lean 定理
- 全部 12 类 BitProgram 指令及任意有限步紧凑执行语义已有通用 Lean 内核证明

**未解决的阻塞**
- 独立全局连接器尚未获得整表等价定理
- 实际带计量 runInstrumented 的循环与指标尚未证明等价

**下一步：** 先给 runInstrumented 构造无计量投影等价定理，再把结构归纳扩展到整套 NativeCodeAssembly 的原版与独立连接器

**证据索引及边界**
- [EV-001](../execution-prototype/native-aftercode-original-20261029/NativeCompactInterpreterProof.lean)（lean_kernel）：runOne_exact 对原版全部 12 类位指令、任意合法状态成立；**限制**：只证明紧凑单步执行器与 BitProgram.execInstr 的语义；不是整套连接器代码等价。
- [EV-002](../execution-prototype/native-aftercode-original-20261029/NativeDirectTraceProof.lean)（lean_kernel）：direct_table_fuel_exact 对任意有限步数成立；sourceArray_is_ofFn 核对原码数组表示；**限制**：这是形式化定义的 directTableFuel，不是带计量的 runInstrumented。
- [EV-003](../execution-prototype/native-aftercode-original-20261029/NativeAfterCodeDirectCertificate.lean)（lean_kernel）：原版 compiled afterCode 的直接取码及任意有限步语义特化定理；**限制**：不证明完整 afterCode 停机；不证明整个 NativeCodeAssembly 的独立连接器。
- [EV-004](../execution-prototype/native-aftercode-original-20261029/primitive-kernel-results.json)（kernel_audit）：8 项 Lean 定理的公理审计符合既定范围；**限制**：这是归档与复现校验的摘要，不替代完整源码和本地 Lean 检查。
- [EV-006](../docs/NATIVE_AFTERCODE_ORIGINAL_20261029.md)（report）：119/119 原版 afterCode 操作码与独立线性化表的运行时一致性；**限制**：局部 119 标签全部比较，不代表完整 NativeCodeAssembly 全标签等价。
- [EV-009](../docs/NATIVE_CANONICAL_START_20261029.md)（report）：原版 canonicalStart 路线及连接器局部标签审计的历史结果；**限制**：部分原版整体编译器位置曾遇昂贵求值或超时。

**关联审阅：** [PR #1](https://github.com/YanZhao1027/3satlocalverify/pull/1) · [PR #2](https://github.com/YanZhao1027/3satlocalverify/pull/2)

---

<a id="g02"></a>
### G02 · 运行代码参数生成

**状态：指定样例通过，非通用** · 难度：中 · 优先级：P1 · 上次复核：2026-10-29

**怎样才算通过**
- 原版 parameters 对真正输入自行计算所有参数、正常停机，输出与独立参考一致
- 记录真实源位步数、完整寄存器／栈状态与峰值；追加涵盖非退化规模的输入回归

**目前证实的范围**
- 在真实 n=3、m=1、B=8 输入上，参数核心执行 9,130 源位指令并停机；记录 7 个参数与 gapDenom
- 已做单程序参数准备的 19,182 步和阶段边界全寄存器／全栈对比

**未解决的阻塞**
- 当前实例很小，不足以支持所有输入的性能或通用鲁棒性

**下一步：** 增加至少一个图维数大于零的真实输入，核对参数、状态、源级成本和可复现脚本

**证据索引及边界**
- [EV-007](../execution-prototype/native-code-parameters-20261029/native-code-assembly-results.json)（runtime）：真实样例参数 9,130 步、图搜索 2,680 步、局部搜索 5,598 步、序列化 715 步；**限制**：特定 n=3、m=1 输入且图维数 r=0；不是任意 CNF 的验收。
- [EV-008](../docs/NATIVE_CODE_PARAMETERS_SEARCHES_20261029.md)（report）：参数、两次源代码搜索、搬运、保存及序列化分阶段执行的来源和限制；**限制**：各阶段通过不等于原版 NativeLeafPreparation.command 整体运行通过。

---

<a id="g03"></a>
### G03 · 运行两个代码搜索程序

**状态：指定样例通过，非通用** · 难度：高 · 优先级：P1 · 上次复核：2026-10-29

**怎样才算通过**
- 原版 NativeCode.searches 两次搜索均从输入真实计算候选结构而非预置答案
- 结果写入物理栈并由独立规格核对，提供非退化图搜索与局部搜索实例

**目前证实的范围**
- 原版图搜索 2,680 步、局部搜索 5,598 步，产生并保存图／局部候选；清理后仍保留搜索结果

**未解决的阻塞**
- 当前图维数 r=0，搜索可能退化；还没有代表性非平凡图结构的完整回归

**下一步：** 构造 r>0 的合法 CNF 及已知结构参照，完整执行两搜索并保留中间位级轨迹

**证据索引及边界**
- [EV-007](../execution-prototype/native-code-parameters-20261029/native-code-assembly-results.json)（runtime）：真实样例参数 9,130 步、图搜索 2,680 步、局部搜索 5,598 步、序列化 715 步；**限制**：特定 n=3、m=1 输入且图维数 r=0；不是任意 CNF 的验收。
- [EV-008](../docs/NATIVE_CODE_PARAMETERS_SEARCHES_20261029.md)（report）：参数、两次源代码搜索、搬运、保存及序列化分阶段执行的来源和限制；**限制**：各阶段通过不等于原版 NativeLeafPreparation.command 整体运行通过。

**依赖关卡：** [G02](#g02)

---

<a id="g04"></a>
### G04 · 完成代码序列化与收尾

**状态：部分证据，未过关** · 难度：中高 · 优先级：P0 · 上次复核：2026-10-29

**怎样才算通过**
- 在真实搜得的结构上执行 serialize 和 afterCode 的所有位指令，正常停机
- 最终物理状态、编码长度和生成内容与原版规格一致；保留含代码表与计量的可复现实测

**目前证实的范围**
- 序列化核心 715 步并把 13 位行数据保存至栈 777
- 直接执行原版 afterCode 8,000,000 步得到 140,962 位编码候选，原始行数据未变，但尚未停机

**未解决的阻塞**
- 完整编码要求 5,120,003 位；afterCode 的完整停机、峰值及末状态没有实测
- 不可使用宿主端一次性填充零串替代原位指令然后声称原版通过

**下一步：** 在硬资源上限内推进 afterCode 的真实执行，分解零候选构造开销；以实际停机与逐状态核对为验收

**证据索引及边界**
- [EV-005](../execution-prototype/native-aftercode-original-20261029/original-aftercode-results.json)（runtime）：实际源程序 afterCode 8,000,000 步产生 140,962 / 5,120,003 编码位且未停机；**限制**：真实单一非空 CNF 的有限前缀；绝非完整停机或全输入资源结论。
- [EV-006](../docs/NATIVE_AFTERCODE_ORIGINAL_20261029.md)（report）：119/119 原版 afterCode 操作码与独立线性化表的运行时一致性；**限制**：局部 119 标签全部比较，不代表完整 NativeCodeAssembly 全标签等价。
- [EV-007](../execution-prototype/native-code-parameters-20261029/native-code-assembly-results.json)（runtime）：真实样例参数 9,130 步、图搜索 2,680 步、局部搜索 5,598 步、序列化 715 步；**限制**：特定 n=3、m=1 输入且图维数 r=0；不是任意 CNF 的验收。
- [EV-008](../docs/NATIVE_CODE_PARAMETERS_SEARCHES_20261029.md)（report）：参数、两次源代码搜索、搬运、保存及序列化分阶段执行的来源和限制；**限制**：各阶段通过不等于原版 NativeLeafPreparation.command 整体运行通过。

**关联审阅：** [PR #1](https://github.com/YanZhao1027/3satlocalverify/pull/1) · [PR #2](https://github.com/YanZhao1027/3satlocalverify/pull/2)

**依赖关卡：** [G02](#g02) · [G03](#g03)

---

<a id="g05"></a>
### G05 · 完整运行 NativeLeafPreparation.command

**状态：未通过** · 难度：高 · 优先级：P0 · 上次复核：2026-10-29

**怎样才算通过**
- 从真实物理编码的 CNF 输入单一原版 compiled 命令，一次性执行至完整查询准备状态
- 全部状态、控制流与完整预算核查通过；中间阶段数据和最终状态不依赖预填答案

**目前证实的范围**
- 已经独立运行并审计前置参数／搜索／序列化子阶段，但没有完整 NativeLeafPreparation.command 停机

**未解决的阻塞**
- 第 4 关 afterCode 没有完成
- 整套原版命令与独立连接器全标签等价未证明

**下一步：** 在关卡 4 停机验证和关卡 1 连接证明之后，执行单程序端到端查询准备并核验全部边界

**证据索引及边界**
- [EV-008](../docs/NATIVE_CODE_PARAMETERS_SEARCHES_20261029.md)（report）：参数、两次源代码搜索、搬运、保存及序列化分阶段执行的来源和限制；**限制**：各阶段通过不等于原版 NativeLeafPreparation.command 整体运行通过。
- [EV-005](../execution-prototype/native-aftercode-original-20261029/original-aftercode-results.json)（runtime）：实际源程序 afterCode 8,000,000 步产生 140,962 / 5,120,003 编码位且未停机；**限制**：真实单一非空 CNF 的有限前缀；绝非完整停机或全输入资源结论。
- [EV-003](../execution-prototype/native-aftercode-original-20261029/NativeAfterCodeDirectCertificate.lean)（lean_kernel）：原版 compiled afterCode 的直接取码及任意有限步语义特化定理；**限制**：不证明完整 afterCode 停机；不证明整个 NativeCodeAssembly 的独立连接器。

**依赖关卡：** [G01](#g01) · [G02](#g02) · [G03](#g03) · [G04](#g04)

---

<a id="g06"></a>
### G06 · 运行高查询核心

**状态：未通过** · 难度：很高 · 优先级：P0 · 上次复核：2026-10-29

**怎样才算通过**
- 真实执行选择器、查询循环和计数服务的原版源位指令，不以 wrapper 或 skip 替代核心
- 有效非空 CNF 进入实际非终止分支；输出／中间状态与独立规格匹配，记录真实步骤和空间

**目前证实的范围**
- 上游高查询路径的非计算性和资源风险已做调查，没有完成真实核心运行

**未解决的阻塞**
- 完整准备状态尚未形成
- HighQueryProgram 的可计算提取与整段动态路径仍未通过

**下一步：** 定位 HighQuery 关键路径中的首个不可计算依赖并在不绕过计算的前提下给出可执行且等价的路径

**证据索引及边界**
- [EV-010](../docs/RESEARCH_OUTLOOK_20261028.md)（report）：HighQuery noncomputable 路径、固定预计算、资源口径和非终止实验的待验证事项；**限制**：方法与风险评估，不是可执行性完成证据。
- [EV-011](../docs/METHODS_AND_LIMITATIONS.md)（report）：形式化结果、实测与资源边界的总约束；**限制**：范围限定性材料，不宣称通用原版 SAT 运行。

**依赖关卡：** [G05](#g05) · [G08](#g08)

---

<a id="g07"></a>
### G07 · 运行完整 SAT/#SAT 求解器

**状态：未通过** · 难度：很高 · 优先级：P1 · 上次复核：2026-10-29

**怎样才算通过**
- 实际运行 OpenAI 原版全链，对一组覆盖 SAT/UNSAT 和不同比例的真实 CNF 输出判定或精确计数
- 精确 #SAT 与独立精确 #SAT 对照；不以只求一个满足赋值的 SAT 结果代替计数

**目前证实的范围**
- 独立桶消元和原版 CRT 局部接口有其他形式化成果，但原版高查询求解器的端到端执行尚不存在

**未解决的阻塞**
- 关卡 5、6 尚未通过
- 性能对照必须匹配精确计数任务

**下一步：** 在真实高查询核心运行之后建立端到端 CNF 输入集和独立精确 #SAT 基线

**证据索引及边界**
- [EV-010](../docs/RESEARCH_OUTLOOK_20261028.md)（report）：HighQuery noncomputable 路径、固定预计算、资源口径和非终止实验的待验证事项；**限制**：方法与风险评估，不是可执行性完成证据。
- [EV-011](../docs/METHODS_AND_LIMITATIONS.md)（report）：形式化结果、实测与资源边界的总约束；**限制**：范围限定性材料，不宣称通用原版 SAT 运行。
- [EV-012](../docs/COMPLEXITY_20261028.md)（report）：独立桶消元的宽度上界与结构性宽度障碍；**限制**：该独立 VE 不是 OpenAI 原版高查询求解器的次指数证明。

**依赖关卡：** [G05](#g05) · [G06](#g06) · [G08](#g08)

---

<a id="g08"></a>
### G08 · 排除隐藏的不可执行依赖

**状态：部分证据，未过关** · 难度：关键难点 · 优先级：P0 · 上次复核：2026-10-29

**怎样才算通过**
- 逐项审计全部被执行路径，没有 SAT.count、语义 oracle、不可计算选择或难以构造的巨大预制答案表
- 所有输入前固定数据和程序表有可复现生成与实际资源成本；若有替代实现必须有语义证明

**目前证实的范围**
- 已执行的位解释器只读取明确 BitProgram 指令；局部 8M 步没有注入答案
- 上游 HighQuery noncomputable、FiniteFallback 的固定表问题已被识别但未全面排除

**未解决的阻塞**
- 尚无完整高查询路径静态与动态调用图清单
- 预计算表的构造、规模、实际运行代价未完整核算

**下一步：** 梳理原版高查询及有限回退的调用图，逐个登记可计算性、表大小、生成方式和运行代价

**证据索引及边界**
- [EV-001](../execution-prototype/native-aftercode-original-20261029/NativeCompactInterpreterProof.lean)（lean_kernel）：runOne_exact 对原版全部 12 类位指令、任意合法状态成立；**限制**：只证明紧凑单步执行器与 BitProgram.execInstr 的语义；不是整套连接器代码等价。
- [EV-010](../docs/RESEARCH_OUTLOOK_20261028.md)（report）：HighQuery noncomputable 路径、固定预计算、资源口径和非终止实验的待验证事项；**限制**：方法与风险评估，不是可执行性完成证据。
- [EV-011](../docs/METHODS_AND_LIMITATIONS.md)（report）：形式化结果、实测与资源边界的总约束；**限制**：范围限定性材料，不宣称通用原版 SAT 运行。
- [EV-013](../docs/NATIVE_LEAF_BRIDGE_20261028.md)（report）：原版叶节点形式化资源契约及预算桥梁的核验；**限制**：证明条件性预算关系，不是实测完整算法或实际净加速。

---

<a id="g09"></a>
### G09 · 严格对应论文 TM2 资源模型

**状态：部分证据，未过关** · 难度：很高 · 优先级：P0 · 上次复核：2026-10-29

**怎样才算通过**
- 对原版的位操作、栈访问、物理寻址、程序表、复制和前置成本建立 TM2 计量对应或上界证明
- 峰值空间和访问成本与 Lean RSS、抽象栈数据位明确区分，避免跨模型偷换

**目前证实的范围**
- 在原版局部实验中统计了位指令、操作码类型和布尔栈数据峰值

**未解决的阻塞**
- 没有全量 TM2 磁带微步/寻址的已证对应
- 没有原版全路径与固定表的完整空间成本

**下一步：** 先形式化 runInstrumented 的源级计量，再验证栈访问与物理 TM2 微步之间的逐类成本对应

**证据索引及边界**
- [EV-005](../execution-prototype/native-aftercode-original-20261029/original-aftercode-results.json)（runtime）：实际源程序 afterCode 8,000,000 步产生 140,962 / 5,120,003 编码位且未停机；**限制**：真实单一非空 CNF 的有限前缀；绝非完整停机或全输入资源结论。
- [EV-008](../docs/NATIVE_CODE_PARAMETERS_SEARCHES_20261029.md)（report）：参数、两次源代码搜索、搬运、保存及序列化分阶段执行的来源和限制；**限制**：各阶段通过不等于原版 NativeLeafPreparation.command 整体运行通过。
- [EV-014](../docs/NATIVE_PHYSICAL_40X896_20261029.md)（report）：40 寄存器、896 栈的物理映射和原生实验测量口径；**限制**：栈数据位峰值未包括 TM2 物理寻址、程序表等全部成本。
- [EV-013](../docs/NATIVE_LEAF_BRIDGE_20261028.md)（report）：原版叶节点形式化资源契约及预算桥梁的核验；**限制**：证明条件性预算关系，不是实测完整算法或实际净加速。

**依赖关卡：** [G01](#g01) · [G04](#g04) · [G08](#g08)

---

<a id="g10"></a>
### G10 · 验证通用次指数复杂度与性能

**状态：未通过** · 难度：最关键 · 优先级：P1 · 上次复核：2026-10-29

**怎样才算通过**
- 形式化审计完整原版算法对所有合法输入的渐近时间／空间上界，含固定程序与预计算成本
- 另在非特制输入上与同任务的精确 #SAT 基线可复现比较，清楚区分定理、上界、实测和优势

**目前证实的范围**
- 已对独立 VE 宽度复杂度建立界限与反例；有原版局部预算桥梁，尚不足以证明全算法优势

**未解决的阻塞**
- 完整运行路径缺失
- 严格 TM2 资源结算不完整
- 有限基准无法证明所有输入的最坏情况次指数时间

**下一步：** 完成关卡 7、8、9 后独立核验论文最坏情况资源证明并设置同任务公开基准

**证据索引及边界**
- [EV-010](../docs/RESEARCH_OUTLOOK_20261028.md)（report）：HighQuery noncomputable 路径、固定预计算、资源口径和非终止实验的待验证事项；**限制**：方法与风险评估，不是可执行性完成证据。
- [EV-012](../docs/COMPLEXITY_20261028.md)（report）：独立桶消元的宽度上界与结构性宽度障碍；**限制**：该独立 VE 不是 OpenAI 原版高查询求解器的次指数证明。
- [EV-013](../docs/NATIVE_LEAF_BRIDGE_20261028.md)（report）：原版叶节点形式化资源契约及预算桥梁的核验；**限制**：证明条件性预算关系，不是实测完整算法或实际净加速。

**依赖关卡：** [G07](#g07) · [G08](#g08) · [G09](#g09)

---

## 状态维护流程

1. Read the board and evidence cards before designing a new experiment.
2. Run the relevant real Lean/Ubuntu verification and preserve raw logs before proposing a status change.
3. Edit only the canonical ten_gates.json; render derived board/cards with scripts/research_board.py --write.
4. Keep accepted scope, remaining blockers, and negative results; do not promote sample to universal.
5. Add dated evidence or corrected limitations and run --check; update research/REVIEW_LOG.md with the change.
6. Never infer that ETH is false or the full #SAT algorithm is complete from local proofs or bounded traces.

查询摘要： `python3 scripts/research_board.py --status`

更新单一可信源后执行： `python3 scripts/research_board.py --write`

交付前验证： `python3 scripts/research_board.py --check`

**重要边界：未完成完整原版高查询 SAT/#SAT，未证明所有输入的次指数优势，也没有证明 ETH 错误。**
