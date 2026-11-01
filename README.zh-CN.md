# Planar Nikodym

[English](README.md)

本项目用 Lean 4 证明平面曲线族的解析分类定理和极大算子估计。定理编号沿用 [arXiv:2609.39217](https://arxiv.org/abs/2609.39217)。

曲线族由以下图像组成：

$$
\Gamma_{z,u}=\{(t,\gamma(t,z,u)):t\in I\},
\qquad I=[a,b],\quad a<b,\quad (z,u)\in W\subset\mathbb R^2\times\mathbb R^d.
$$

[结果目录](docs/RESULTS.zh-CN.md)列出数学陈述、假设及对应的 Lean 声明。

## 分类定理

| 结果 | 陈述与假设 |
|---|---|
| **定理 1.4** | 若参数域为开集，定义函数在 $I\times\overline W$ 的邻域内解析，则该曲线族容许 Nikodym 集，当且仅当它存在大规模曲线复用，或存在不能被可数个光滑叶状结构覆盖的局部复用。 |
| **定理 1.5** | 若参数域为非空有界开集，定义函数解析，且点秩与曲线秩均为常数，则四种秩情形决定 Nikodym 集的存在性、曲线复用和叶状结构覆盖情况。 |
| **命题 1.6** | 对于定理所规定的解析参数域，存在有限个连通、解析、恒秩的曲线族，保留 Nikodym 集存在性和大规模曲线复用。当原曲线族不存在大规模曲线复用时，它们还保留未被覆盖的局部复用。时间区间保持不变，辅助维数不增加。 |
| **推论 1.2** | 在任意辅助维数 $d\ge0$ 下，开参数域上满足 cinematic 非退化条件的光滑曲线族均不容许 Nikodym 集。 |

公开声明：`theorem_1_4_proved`、`theorem_1_5_proved`、`proposition_1_6_paper_proved` 和 `corollary_1_2_smooth`。

## 极大估计与局部光滑化

设参数域为开集，定义函数在原闭时间区间上光滑，且 $K\subset W$ 是紧参数集。假设在 $I\times K$ 上满足 cinematic 非退化条件。原区间极大算子在以下有限指数范围内具有有界的 Lipschitz $L^p\to L^p$ 实现：

| 维数 | 指数 | Lean 声明 |
|---|---|---|
| $d=1$ | $2<p<\infty$ | `Family.theorem_1_1_one_auxiliary_proved` |
| 任意 $d\ge0$ | $(d+1)(d+2)\le p<\infty$ | `Family.theorem_1_1_high_p_proved` |

这些实现在连续紧支撑函数上与逐点定义的算子几乎处处相等。闭域上的 cinematic 非退化条件使用定义域内的典范 jet 表述。

**定理 2.1 和推论 2.2** 对任意 $d\ge0$ 和有限指数 $p\ge(d+1)(d+2)$ 给出局部光滑化估计与极大频率估计。对于全局光滑的相位、满足 cinematic 非退化条件的一点的一个固定且充分小的邻域、支撑于该邻域内的实值光滑紧支撑截断函数，以及 $f\in L^1\cap L^p$，相应频率因子分别为

$$
2^{(-(d+1)/p+\varepsilon)k}
\qquad\text{和}\qquad
2^{(-1/p+\varepsilon)k},\qquad \varepsilon>0.
$$

**引理 2.3** 给出光滑 cinematic 非退化相位所对应的精确尺度解耦定理，其 $L^2$ 误差快速衰减。

## 解析结构结果

本库还证明了非退化有界闭区间上的解析 Wronskian 判据（**定理 5.3**）、解析系数表示（**引理 5.6**）、冗余参数消去（**引理 6.1**）、有效维数约化与中心切片约化（**推论 6.2–6.3**），以及可数光滑切向量场覆盖（**引理 7.1**）。

## 构建与验证

项目固定使用 Lean `v4.32.0-rc1` 和 Mathlib 提交 `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`。

在已安装 Git、Python 3 和 Lean 工具链管理器的环境中，于仓库根目录运行：

```sh
lake exe cache get
bash scripts/check.sh
```

检查程序会构建本库，并审计各声明的传递公理依赖。允许使用的逻辑公理为 `propext`、`Classical.choice` 和 `Quot.sound`。[GitHub 工作流](.github/workflows/lean.yml)在推送和拉取请求时执行相同检查。

通过以下方式使用本库：

```lean
import PlanarNikodym
```

- [精确定理陈述与 Lean 声明](docs/RESULTS.zh-CN.md)
- [构建、验证与维护](docs/BUILD.md)
- [源模块索引](docs/MODULE_INDEX.md)
- [验证流程](verification/README.md)
