# 已形式化的结果

[English](RESULTS.md)

本目录陈述公开 Lean 声明所提供的数学结果，包括其假设和指数范围。下文所有声明名均位于 `PlanarNikodym` 命名空间内。源码链接给出了完整的 Lean 陈述。

对于平面曲线族，记

$$
I=[a,b],\qquad a<b,\qquad
W\subset\mathbb R^2\times\mathbb R^d,\qquad
\Gamma_{z,u}=\{(t,\gamma(t,z,u)):t\in I\}.
$$

辅助维数 $d$ 为自然数，允许为零。在一个集合上解析，是指在该集合每一点的环境邻域内解析，包括时间端点。点秩是将 $\gamma$ 关于辅助参数的偏导数视为 $I$ 上的函数后，其张成空间的维数；曲线秩还将关于两个中心坐标的偏导数包括在内。

几何术语定义于 [Definitions.lean](../PlanarNikodym/Core/Definitions.lean)。具体而言：

- $N(G)$：存在 Borel 集 $E,F\subset\mathbb R^2$，满足 $|E|=0$、$|F|>0$，且对每个 $z\in F$，都存在某个 $u$，使得 $(z,u)\in W$ 且 $\mathcal H^1(E\cap\Gamma_{z,u})>0$。
- $M(G)$：存在一条固定曲线，其对应的中心集合具有正的平面内测度（大规模曲线复用）。
- 一个参数称为局部复用的，是指在该参数的每个邻域内，都能在一个具有正的一维 Hausdorff 内测度的中心集合上得到同一条曲线。
- $U(G)$：对于每个可数的光滑平面向量场族，存在局部复用曲线且该曲线未被这些向量场覆盖的中心所成的集合，都具有正的平面内测度。覆盖是指在曲线上 Hausdorff 几乎处处的点，至少一个向量场非零且与曲线相切。

**定理 1.4——解析分类。**

设 $W$ 为开集，且 $\gamma$ 在 $I\times\overline W$ 的邻域内解析。则

$$
N(G)\quad\Longleftrightarrow\quad M(G)\ \lor\ U(G).
$$

声明：`theorem_1_4_proved`，位于 [GeneralAnalyticClassification.lean](../PlanarNikodym/Classification/GeneralAnalyticClassification.lean)。其陈述为 [Statements.lean](../PlanarNikodym/Core/Statements.lean) 中的 `Theorem14Statement`。

**定理 1.5——点秩与曲线秩恒定时的分类。**

设 $W$ 非空、开且有界。假设 $\gamma$ 在 $I\times W$ 的邻域内解析，点秩 $m_p$ 和曲线秩 $m_c$ 在 $W$ 上恒定。则有以下结论：

| 秩之间的关系 | 结论 |
|---|---|
| $m_c=m_p+2$ | $N(G)$ 不成立，且族内每条曲线都不被复用。 |
| $m_c=m_p+1, m_p=0$ | $N(G)$ 和 $M(G)$ 均不成立；每个参数都局部复用，且所有被复用的曲线都由同一个可数光滑向量场族覆盖。 |
| $m_c=m_p+1, m_p>0$ | $N(G)$ 成立，存在局部曲线复用，且 $U(G)$ 成立。 |
| $m_c=m_p$ | $N(G)$ 和 $M(G)$ 均成立。 |

声明：`theorem_1_5_proved`，位于 [ProvedAnalyticClassification.lean](../PlanarNikodym/Classification/ProvedAnalyticClassification.lean)。上述四种结论由 [Statements.lean](../PlanarNikodym/Core/Statements.lean) 中的 `ConstantRankConclusions` 编码。

**命题 1.6——有限个常秩见证族。**

设 $W$ 开且有界，并假设 $W$ 是正半径的球，或者

$$
W=\{q:f(q)<0\},
$$

其中 $f$ 在 $\overline W$ 的邻域内解析。假设 $\gamma$ 在 $I\times\overline W$ 的邻域内解析。

存在有限个曲线族 $H_i$，每个族的参数域都开、有界且连通，定义函数解析，点秩与曲线秩恒定，时间区间均为同一个 $I$，辅助维数满足 $d_i\le d$，并且

$$
\begin{aligned}
N(G)&\Longleftrightarrow \exists i\ N(H_i),\\
M(G)&\Longleftrightarrow \exists i\ M(H_i),\\
\neg M(G)&\Longrightarrow
  \bigl(U(G)\Longleftrightarrow \exists i\ U(H_i)\bigr).
\end{aligned}
$$

声明：`proposition_1_6_paper_proved`，其陈述为 `Proposition16PaperStatement`，均位于 [PaperProposition16.lean](../PlanarNikodym/Classification/PaperProposition16.lean)。参数域假设为 [RankDecomposition.lean](../PlanarNikodym/Cells/RankDecomposition.lean) 中的 `AnalyticParameterDomain`。

**推论 1.2——光滑 cinematic 曲线族不存在 Nikodym 集。**

设 $W$ 为开集，$\gamma\in C^\infty(I\times W)$。如果 cinematic 行列式在 $I\times W$ 的每一点均非零，则 $N(G)$ 不成立。此结论适用于所有辅助维数 $d\ge0$。

声明：`corollary_1_2_smooth`，位于 [E3SmoothMaximalExclusion.lean](../PlanarNikodym/Analysis/Maximal/E3SmoothMaximalExclusion.lean)。这里的假设使用了 [Cinematic.lean](../PlanarNikodym/Geometry/Cinematic.lean) 中由环境导数定义的 `Family.cinematicDet`，以及闭域上的光滑性谓词 `Family.IsSmooth`。

**定理 1.1——原时间区间上极大算子的有界性。**

设 $W$ 为开集，$\gamma\in C^\infty(I\times W)$，且 $K\subset W$ 为紧集。假设由定义域内的典范 jet 构成的 cinematic 行列式在 $I\times K$ 上非零。对于连续紧支撑函数，定义

$$
M_K f(z)=\sup_{u:(z,u)\in K}
\left|\int_I f(t,\gamma(t,z,u))\,dt\right|,
$$

参数纤维为空时取值为零。存在 $C\ge0$ 和映射

$$
T:L^p(\mathbb R^2;\mathbb C)\longrightarrow L^p(\mathbb R^2;\mathbb C)
$$

满足 $T0=0$、$\|Tf-Tg\|_p\le C\|f-g\|_p$、$\|Tf\|_p\le C\|f\|_p$，且对于每个连续紧支撑测试函数，都有 $Tf=M_Kf$ 几乎处处成立。已经证明的有限指数范围如下：

| 维数与指数 | 声明 |
|---|---|
| $d=1, 2<p<\infty$ | `Family.theorem_1_1_one_auxiliary_proved`，位于 [OneAuxiliaryOriginalMaximal.lean](../PlanarNikodym/Analysis/Maximal/OneAuxiliaryOriginalMaximal.lean) |
| $d\ge0, (d+1)(d+2)\le p<\infty$ | `Family.theorem_1_1_high_p_proved`，位于 [SmoothHighPMaximal.lean](../PlanarNikodym/Analysis/Maximal/SmoothHighPMaximal.lean) |

闭域行列式为 `Family.cinematicDetWithin_e2`；[E2WithinCinematic.lean](../PlanarNikodym/Analysis/Maximal/E2WithinCinematic.lean) 证明，在定义函数于邻域内光滑时，该行列式与环境行列式相同。极大算子定义于 [E2IntervalMaximal.lean](../PlanarNikodym/Analysis/Maximal/E2IntervalMaximal.lean)。

**定理 2.1 与推论 2.2——局部光滑化与极大算子频率估计。**

假设 $\gamma$ 在全部变量上联合全局 $C^\infty$，且其 cinematic 行列式在某点 $x$ 非零。存在一个在截断函数及指数之前选定的开邻域 $O\ni x$，具有以下性质。对于每个满足 $\operatorname{tsupport}\chi\subset O$ 的实值函数 $\chi\in C_c^\infty$、每个 `FrequencyCutoff` $P_k$、每个有限的 $p$ 以及 $\varepsilon$，其中

$$
p\ge(d+1)(d+2),\qquad \varepsilon>0,
$$

存在不依赖于 $k\ge0$ 及 $f\in L^1(\mathbb R^2)\cap L^p(\mathbb R^2)$ 的常数，使得

$$
\begin{aligned}
\|A_\chi P_kf\|_{L^p(\mathbb R^{d+2})}
&\le C\,2^{(-(d+1)/p+\varepsilon)k}\|f\|_p,\\
\|M_\chi P_kf\|_{L^p(\mathbb R^2)}
&\le C'\,2^{(-1/p+\varepsilon)k}\|f\|_p.
\end{aligned}
$$

这里 $A_\chi f(z,u)=\int_{\mathbb R}\chi(t,z,u)f(t,\gamma(t,z,u))\,dt$，且 $M_\chi f(z)=\sup_u|A_\chi f(z,u)|$。实值截断函数允许变号，且结论包括 $d=0$ 的情况。

声明：`Family.theorem_2_1_smooth_proved` 与 `Family.corollary_2_2_smooth_proved`，位于 [SmoothLocalSmoothing.lean](../PlanarNikodym/Analysis/Maximal/SmoothLocalSmoothing.lean)。

**引理 2.3——光滑 cinematic 相位的精确尺度解耦。**

设 $K\subset U\subset\mathbb R\times\mathbb R^{d+2}$，其中 $K$ 为紧集，$U$ 为开集。假设相位在 $U$ 上联合 $C^\infty$，cinematic 非退化条件在 $K$ 上成立，且 $K$ 在时间轴上的投影包含于 $(-1,1)$。设复值振幅 $a\in C_c^\infty$ 在时间与参数变量上的支撑包含于 $K$。

对于有限的 $p\ge(d+1)(d+2)$、$\varepsilon>0$、$Q\ge0$ 及固定的 $0<r_{\min}\le r_{\max}$，存在 $C>0$，使得对于每个 $r\ge1$ 及每个支撑包含于 $[-1,1]\times[r_{\min},r_{\max}]$ 的 $L^2$ 输入 $g$，都有

$$
\|E_rg\|_p\le
C r^{\beta(d+1,p)+\varepsilon}
\left(\sum_i\|E_{r,i}g\|_p^p\right)^{1/p}
+C r^{-Q}\|g\|_2,
\qquad
\beta(n,p)=\frac{1-1/p-n(n+1)/(2p)}{n}.
$$

$E_{r,i}$ 是使用尺度为 $\delta=r^{-1/(d+1)}$ 的光滑窗口构成的实际时间切片延拓算子；窗口中心为 $c_i=-1+i\delta$，支撑包含于 $[c_i-\delta,c_i+\delta]$。相邻中心的间距为 $\delta$。窗口和切片算子分别定义于 [ScaleTimePartition.lean](../PlanarNikodym/Analysis/Localization/ScaleTimePartition.lean) 与 [TimeSliceExtension.lean](../PlanarNikodym/Analysis/Fourier/TimeSliceExtension.lean)。左侧使用的相位、振幅和输入与这些切片中使用的相同。常数在 $r$ 和 $g$ 之前选定。

声明：`Family.lemma_2_3`，位于 [GlyzLemma23.lean](../PlanarNikodym/Analysis/Fourier/GlyzLemma23.lean)。指数定义于 [DecouplingExponents.lean](../PlanarNikodym/Analysis/Fourier/DecouplingExponents.lean)。

**定理 5.3——解析 Wronskian 判别准则。**

对于在非退化有界闭区间 $I$ 的邻域内解析的任意有限实值函数族，

$$
\{f_j|_I\}_j\text{ 线性相关}
\quad\Longleftrightarrow\quad
\operatorname{Wr}(f_1,\ldots,f_n)(t)=0
\text{ 对每个 }t\in I\text{ 成立}.
$$

该陈述包括两个时间端点和空函数族。声明：`theorem_5_3`，位于 [WronskianCriterion.lean](../PlanarNikodym/Rank/WronskianCriterion.lean)。

**引理 5.6——张成空间维数恒定时的解析系数。**

设 $I\subset\mathbb R$，$W$ 是实赋范向量空间中的开集，且 $q\in W$。假设有限函数族 $f_1,\ldots,f_m$ 与 $g_1,\ldots,g_n$ 在 $I\times W$ 的邻域内联合解析。假设对于 $q$ 附近的参数，$f_j$ 在 $I$ 上的张成空间维数为 $m$，且所有 $f_j,g_i$ 的张成空间具有相同维数。则存在 $q$ 的开邻域 $V\subset W$ 和解析系数 $C_{ij}:V\to\mathbb R$，使得

$$
g_i(t,w)=\sum_{j=1}^m C_{ij}(w)f_j(t,w)
\qquad(w\in V,\ t\in I).
$$

声明：`lemma_5_6_interval`，位于 [Lemma56.lean](../PlanarNikodym/Rank/Lemma56.lean)。

**引理 6.1——冗余参数的解析消去。**

将参数写成 $(v,w,\eta)\in\mathbb R^a\times\mathbb R^b\times\mathbb R^c$。设 $W$ 为开集，$q\in W$，并假设 $\varphi(t,v,w,\eta)$ 在 $I\times W$ 的邻域内联合解析。假设在参数域的每一点，将关于 $w$ 的偏导数视为 $I$ 上的函数时，其张成空间维数为 $b$，且加入关于 $\eta$ 的偏导数后该维数保持不变。

存在一个具有解析逆映射的局部解析坐标变换，

$$
e(v,w,\eta)=(v,\kappa(v,w,\eta),\eta),
$$

其定义域为以 $q$ 为中心的一个球，定义域和值域均包含于 $W$，并满足

$$
\varphi(t,e(v,w,\eta))=\varphi(t,v,w,\eta_q),
\qquad
\kappa(v,w,\eta_q)=w.
$$

第一式对 $(v,w,\eta)\in e.\mathrm{source}$ 且 $t\in I$ 成立；第二式对 $(v,w,\eta_q)\in e.\mathrm{source}$ 成立。

声明：`lemma_6_1_interval`，位于 [Lemma61.lean](../PlanarNikodym/Reduction/Lemma61.lean)。

**推论 6.2——约化到有效辅助维数。**

对于开参数域上的解析族，若点秩恒为 $m$、曲线秩恒为 $k$，则每个参数点都有一个邻域，使该族在此邻域内可用 $m$ 个辅助变量表示。约化后的参数域是开中心域与开辅助域之积，时间区间及两种秩保持不变，并且在每个中心上对应的曲线集合完全相同。

声明：`corollary_6_2`，位于 [FamilyReduction.lean](../PlanarNikodym/Reduction/FamilyReduction.lean)。

**推论 6.3——中心切片正规形。**

设开参数域上的解析族处处具有点秩 $d$ 和曲线秩 $d+1$。在每个参数点附近，可以选取一个有效中心坐标，并构造具有解析逆映射的解析坐标变换，将该族与冻结另一个中心坐标所得切片上的族等同起来。该变换保留这一互补坐标，并在所选切片上等于恒等映射。

声明：`corollary_6_3` 与 `corollary_6_3_functions`，位于 [CenterReduction.lean](../PlanarNikodym/Reduction/CenterReduction.lean)。

**引理 7.1——可数光滑切向量场覆盖。**

假设 $h(t,s)$ 在 $I\times J$ 的邻域内解析，其中 $I$ 为非退化有界闭区间，且对每个 $s\in J$，函数 $t\mapsto\partial_s h(t,s)$ 在 $I$ 上不恒为零。存在同一个可数族的全局光滑平面向量场，使得对于每条曲线 $t\mapsto(t,h(t,s))$，除了依赖于 $s$ 的有限个时间以外，都由这些向量场的非零切方向覆盖。特别地，在每条曲线上，对几乎所有时间都有这种覆盖。

声明：`lemma_7_1` 与 `lemma_7_1_finite_exceptions`，位于 [Lemma71.lean](../PlanarNikodym/Classification/Lemma71.lean)。
