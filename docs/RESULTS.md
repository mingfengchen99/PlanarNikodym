# Formalized results

[简体中文](RESULTS.zh-CN.md)

This catalog states the mathematical results provided by the public Lean declarations, with their hypotheses and exponent ranges. All declaration names below are in the `PlanarNikodym` namespace. The source links give the complete Lean statements.

For a planar curve family, write

$$
I=[a,b],\qquad a<b,\qquad
W\subset\mathbb R^2\times\mathbb R^d,\qquad
\Gamma_{z,u}=\{(t,\gamma(t,z,u)):t\in I\}.
$$

The auxiliary dimension $d$ is a natural number and may be zero. Analyticity on a set means analyticity in an ambient neighborhood of each point, including the time endpoints. The point rank is the dimension of the span of the auxiliary parameter derivatives of $\gamma$, viewed as functions on $I$; the curve rank also includes the two center derivatives.

The geometric terminology is defined in [Definitions.lean](../PlanarNikodym/Core/Definitions.lean). In particular:

- $N(G)$: there exist Borel sets $E,F\subset\mathbb R^2$ with $|E|=0$ and $|F|>0$ such that, for every $z\in F$, some $u$ satisfies $(z,u)\in W$ and $\mathcal H^1(E\cap\Gamma_{z,u})>0$.
- $M(G)$: one fixed curve is associated with a set of centers of positive inner planar measure (massive curve reuse).
- A parameter is locally reused when every parameter neighborhood supplies that same curve at a set of centers of positive inner one-dimensional Hausdorff measure.
- $U(G)$: for every countable collection of smooth planar vector fields, the centers admitting a locally reused curve not covered by those fields have positive inner planar measure. Coverage means that, at Hausdorff-almost every point of the curve, one of the fields is nonzero and tangent to it.

**Theorem 1.4 — analytic classification.**

Let $W$ be open, and suppose $\gamma$ is analytic on a neighborhood of $I\times\overline W$. Then

$$
N(G)\quad\Longleftrightarrow\quad M(G)\ \lor\ U(G).
$$

Declaration: `theorem_1_4_proved`, in [GeneralAnalyticClassification.lean](../PlanarNikodym/Classification/GeneralAnalyticClassification.lean). Its statement is `Theorem14Statement` in [Statements.lean](../PlanarNikodym/Core/Statements.lean).

**Theorem 1.5 — classification at constant point and curve ranks.**

Let $W$ be nonempty, open and bounded. Suppose $\gamma$ is analytic on a neighborhood of $I\times W$, and the point rank $m_p$ and curve rank $m_c$ are constant on $W$. The following conclusions hold:

| Rank relation | Conclusion |
|---|---|
| $m_c=m_p+2$ | $N(G)$ is false, and every curve in the family is not reused. |
| $m_c=m_p+1, m_p=0$ | $N(G)$ and $M(G)$ are false; every parameter is locally reused, and all reused curves are covered by one countable collection of smooth vector fields. |
| $m_c=m_p+1, m_p>0$ | $N(G)$ holds, local curve reuse occurs, and $U(G)$ holds. |
| $m_c=m_p$ | $N(G)$ and $M(G)$ hold. |

Declaration: `theorem_1_5_proved`, in [ProvedAnalyticClassification.lean](../PlanarNikodym/Classification/ProvedAnalyticClassification.lean). The four conclusions are encoded by `ConstantRankConclusions` in [Statements.lean](../PlanarNikodym/Core/Statements.lean).

**Proposition 1.6 — finite constant-rank witnesses.**

Let $W$ be open and bounded, and suppose either that $W$ is a ball of positive radius, or that

$$
W=\{q:f(q)<0\},
$$

where $f$ is analytic on a neighborhood of $\overline W$. Suppose $\gamma$ is analytic on a neighborhood of $I\times\overline W$.

There are finitely many families $H_i$, each with an open, bounded, connected parameter domain, analytic defining function, constant point and curve ranks, the same time interval $I$, and auxiliary dimension $d_i\le d$, such that

$$
\begin{aligned}
N(G)&\Longleftrightarrow \exists i\ N(H_i),\\
M(G)&\Longleftrightarrow \exists i\ M(H_i),\\
\neg M(G)&\Longrightarrow
  \bigl(U(G)\Longleftrightarrow \exists i\ U(H_i)\bigr).
\end{aligned}
$$

Declaration: `proposition_1_6_paper_proved`, with statement `Proposition16PaperStatement`, in [PaperProposition16.lean](../PlanarNikodym/Classification/PaperProposition16.lean). The domain hypothesis is `AnalyticParameterDomain` in [RankDecomposition.lean](../PlanarNikodym/Cells/RankDecomposition.lean).

**Corollary 1.2 — smooth cinematic families exclude Nikodym sets.**

Let $W$ be open and $\gamma\in C^\infty(I\times W)$. If the cinematic determinant is nonzero at every point of $I\times W$, then $N(G)$ is false. This applies in every auxiliary dimension $d\ge0$.

Declaration: `corollary_1_2_smooth`, in [E3SmoothMaximalExclusion.lean](../PlanarNikodym/Analysis/Maximal/E3SmoothMaximalExclusion.lean). Here the hypothesis uses `Family.cinematicDet`, defined from ambient derivatives in [Cinematic.lean](../PlanarNikodym/Geometry/Cinematic.lean), together with the closed-domain smoothness predicate `Family.IsSmooth`.

**Theorem 1.1 — bounds for the original interval maximal operator.**

Let $W$ be open, $\gamma\in C^\infty(I\times W)$, and $K\subset W$ be compact. Assume that the cinematic determinant formed from the canonical within-domain jets is nonzero on $I\times K$. On continuous compactly supported functions, set

$$
M_K f(z)=\sup_{u:(z,u)\in K}
\left|\int_I f(t,\gamma(t,z,u))\,dt\right|,
$$

with value zero on an empty parameter fiber. There exist $C\ge0$ and a map

$$
T:L^p(\mathbb R^2;\mathbb C)\longrightarrow L^p(\mathbb R^2;\mathbb C)
$$

such that $T0=0$, $\|Tf-Tg\|_p\le C\|f-g\|_p$, $\|Tf\|_p\le C\|f\|_p$, and $Tf=M_Kf$ almost everywhere for every continuous compactly supported test function. The proved finite-exponent ranges are:

| Dimension and exponent | Declaration |
|---|---|
| $d=1, 2<p<\infty$ | `Family.theorem_1_1_one_auxiliary_proved`, in [OneAuxiliaryOriginalMaximal.lean](../PlanarNikodym/Analysis/Maximal/OneAuxiliaryOriginalMaximal.lean) |
| $d\ge0, (d+1)(d+2)\le p<\infty$ | `Family.theorem_1_1_high_p_proved`, in [SmoothHighPMaximal.lean](../PlanarNikodym/Analysis/Maximal/SmoothHighPMaximal.lean) |

The closed-domain determinant is `Family.cinematicDetWithin_e2`; [E2WithinCinematic.lean](../PlanarNikodym/Analysis/Maximal/E2WithinCinematic.lean) identifies it with the ambient determinant when the defining function is smooth in a neighborhood. The maximal operator is defined in [E2IntervalMaximal.lean](../PlanarNikodym/Analysis/Maximal/E2IntervalMaximal.lean).

**Theorem 2.1 and Corollary 2.2 — local smoothing and maximal frequency estimates.**

Suppose $\gamma$ is globally jointly $C^\infty$, and its cinematic determinant is nonzero at a point $x$. There is an open neighborhood $O\ni x$, chosen before the cutoff and exponents, with the following property. For every real-valued $\chi\in C_c^\infty$ with $\operatorname{tsupport}\chi\subset O$, every `FrequencyCutoff` $P_k$, every finite

$$
p\ge(d+1)(d+2),\qquad \varepsilon>0,
$$

there are constants independent of $k\ge0$ and $f\in L^1(\mathbb R^2)\cap L^p(\mathbb R^2)$ such that

$$
\begin{aligned}
\|A_\chi P_kf\|_{L^p(\mathbb R^{d+2})}
&\le C\,2^{(-(d+1)/p+\varepsilon)k}\|f\|_p,\\
\|M_\chi P_kf\|_{L^p(\mathbb R^2)}
&\le C'\,2^{(-1/p+\varepsilon)k}\|f\|_p.
\end{aligned}
$$

Here $A_\chi f(z,u)=\int_{\mathbb R}\chi(t,z,u)f(t,\gamma(t,z,u))\,dt$ and $M_\chi f(z)=\sup_u|A_\chi f(z,u)|$. Signed real cutoffs are allowed, and $d=0$ is included.

Declarations: `Family.theorem_2_1_smooth_proved` and `Family.corollary_2_2_smooth_proved`, in [SmoothLocalSmoothing.lean](../PlanarNikodym/Analysis/Maximal/SmoothLocalSmoothing.lean).

**Lemma 2.3 — exact-scale decoupling for smooth cinematic phases.**

Let $K\subset U\subset\mathbb R\times\mathbb R^{d+2}$, with $K$ compact and $U$ open. Suppose the phase is jointly $C^\infty$ on $U$, cinematic nondegeneracy holds on $K$, and the time projection of $K$ lies in $(-1,1)$. Let the complex amplitude $a\in C_c^\infty$ have its time–parameter support in $K$.

For finite $p\ge(d+1)(d+2)$, $\varepsilon>0$, $Q\ge0$, and fixed $0<r_{\min}\le r_{\max}$, there is $C>0$ such that, for every $r\ge1$ and every $L^2$ input $g$ supported in $[-1,1]\times[r_{\min},r_{\max}]$,

$$
\|E_rg\|_p\le
C r^{\beta(d+1,p)+\varepsilon}
\left(\sum_i\|E_{r,i}g\|_p^p\right)^{1/p}
+C r^{-Q}\|g\|_2,
\qquad
\beta(n,p)=\frac{1-1/p-n(n+1)/(2p)}{n}.
$$

The $E_{r,i}$ are the actual time-sliced extension operators formed using smooth windows at scale $\delta=r^{-1/(d+1)}$, with centers $c_i=-1+i\delta$ and support contained in $[c_i-\delta,c_i+\delta]$. Adjacent centers are spaced by $\delta$. The windows and sliced operators are defined in [ScaleTimePartition.lean](../PlanarNikodym/Analysis/Localization/ScaleTimePartition.lean) and [TimeSliceExtension.lean](../PlanarNikodym/Analysis/Fourier/TimeSliceExtension.lean). The phase, amplitude and input on the left are the same ones used in those slices. The constant precedes both $r$ and $g$.

Declaration: `Family.lemma_2_3`, in [GlyzLemma23.lean](../PlanarNikodym/Analysis/Fourier/GlyzLemma23.lean). The exponent is defined in [DecouplingExponents.lean](../PlanarNikodym/Analysis/Fourier/DecouplingExponents.lean).

**Theorem 5.3 — the analytic Wronskian criterion.**

For every finite family of real-valued functions analytic on a neighborhood of the nondegenerate bounded closed interval $I$,

$$
\{f_j|_I\}_j\text{ is linearly dependent}
\quad\Longleftrightarrow\quad
\operatorname{Wr}(f_1,\ldots,f_n)(t)=0
\text{ for every }t\in I.
$$

The statement includes both time endpoints and the empty function family. Declaration: `theorem_5_3`, in [WronskianCriterion.lean](../PlanarNikodym/Rank/WronskianCriterion.lean).

**Lemma 5.6 — analytic coefficients for a family of constant span.**

Let $I\subset\mathbb R$, let $W$ be open in a real normed vector space, and let $q\in W$. Suppose finite families $f_1,\ldots,f_m$ and $g_1,\ldots,g_n$ are jointly analytic on a neighborhood of $I\times W$. Assume that, for parameters near $q$, the span of the $f_j$ on $I$ has dimension $m$, and the span of all $f_j,g_i$ has the same dimension. Then there is an open neighborhood $V\subset W$ of $q$ and analytic coefficients $C_{ij}:V\to\mathbb R$ such that

$$
g_i(t,w)=\sum_{j=1}^m C_{ij}(w)f_j(t,w)
\qquad(w\in V,\ t\in I).
$$

Declaration: `lemma_5_6_interval`, in [Lemma56.lean](../PlanarNikodym/Rank/Lemma56.lean).

**Lemma 6.1 — analytic elimination of redundant parameters.**

Write the parameters as $(v,w,\eta)\in\mathbb R^a\times\mathbb R^b\times\mathbb R^c$. Let $W$ be open, $q\in W$, and suppose $\varphi(t,v,w,\eta)$ is jointly analytic on a neighborhood of $I\times W$. At every parameter point, assume that the span, as functions on $I$, of the $w$-derivatives has dimension $b$, and adjoining the $\eta$-derivatives leaves that dimension unchanged.

There is a local analytic coordinate map with analytic inverse,

$$
e(v,w,\eta)=(v,\kappa(v,w,\eta),\eta),
$$

defined on a ball about $q$, with source and target in $W$, such that

$$
\varphi(t,e(v,w,\eta))=\varphi(t,v,w,\eta_q),
\qquad
\kappa(v,w,\eta_q)=w.
$$

The first identity holds for $(v,w,\eta)\in e.\mathrm{source}$ and $t\in I$; the second holds for $(v,w,\eta_q)\in e.\mathrm{source}$.

Declaration: `lemma_6_1_interval`, in [Lemma61.lean](../PlanarNikodym/Reduction/Lemma61.lean).

**Corollary 6.2 — reduction to the effective auxiliary dimension.**

For an analytic family on an open parameter domain with constant point rank $m$ and constant curve rank $k$, every parameter point has a neighborhood on which the family can be represented using $m$ auxiliary variables. The reduced domain is a product of open center and auxiliary domains, the time interval and both ranks are preserved, and the sets of curves at each center agree exactly.

Declaration: `corollary_6_2`, in [FamilyReduction.lean](../PlanarNikodym/Reduction/FamilyReduction.lean).

**Corollary 6.3 — the center-slice normal form.**

Let an analytic family on an open parameter domain have point rank $d$ and curve rank $d+1$ everywhere. Near each parameter point, one can choose an effective center coordinate and construct an analytic coordinate map with analytic inverse that identifies the family with the slice obtained by freezing the other center coordinate. The map preserves that complementary coordinate and is the identity on the distinguished slice.

Declarations: `corollary_6_3` and `corollary_6_3_functions`, in [CenterReduction.lean](../PlanarNikodym/Reduction/CenterReduction.lean).

**Lemma 7.1 — countable smooth tangent-field coverage.**

Suppose $h(t,s)$ is analytic on a neighborhood of $I\times J$, where $I$ is a nondegenerate bounded closed interval, and for each $s\in J$ the function $t\mapsto\partial_s h(t,s)$ is not identically zero on $I$. There is one countable collection of globally smooth planar vector fields such that every curve $t\mapsto(t,h(t,s))$ is covered by their nonzero tangent directions outside a finite set of times depending on $s$. In particular, coverage holds for almost every time on each curve.

Declarations: `lemma_7_1` and `lemma_7_1_finite_exceptions`, in [Lemma71.lean](../PlanarNikodym/Classification/Lemma71.lean).
