# 本地 3-SAT / #SAT 复现与 Lean 形式化验证

本仓库记录 2026-10-28 在个人 Ubuntu 计算机完成的独立实验，基于 [OpenAI/math](https://github.com/openai/math) SubexponentialSAT 形式化源码。本仓库**不是**完整论文次指数算法的实现，也没有独立证明 ETH 为假。

## 已完成的成果

- 任意有限 CNF 的 Lean 桶式变量消元语义及整数 #SAT 正确性证明。
- 有证明的缓存优化、对偶数一阶 Hermite 采样及导数正确性。
- 接入 OpenAI 原版 `Reconstruction.run_correct` 的条件性重构与精确计数证明。
- 对模 2401 的代数假设作具体证明，11 变量连通 3-SAT 实例已通过 `eleven_input_original_CRT_exact` 内核检查。
- 公理审计仅依赖 `propext`、`Classical.choice`、`Quot.sound`，不使用额外的 `native_decide` 公理。
- Python 变量消元 277/277 测试通过；Lean 缓存 Hermite/CRT 随机连通实例 84/84 通过。
- 低宽度连通 64 变量、62 子句实例的精确计数为 11,370,557,917,191,032。

核心源码位于 `execution-prototype/general-ve-20261028/`；参考 [复现指南](docs/REPRODUCE.md)、[研究边界](docs/METHODS_AND_LIMITATIONS.md)、[同步方法](docs/SYNC.md)。

## 范围

变量消元在最坏情况下仍可能需要指数时间和空间。当前实验**不能展示一般 SAT 的最坏情况次指数时间优势**。外部 DIMACS 解析器和 Python 原型有测试，但尚未获得相同级别的 Lean 内核证明。OpenAI 原仓库和依赖需单独安装。本独立仓库目前未选定版权许可协议。