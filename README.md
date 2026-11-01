# Planar Nikodym

[中文](README.zh-CN.md)

Lean 4 proofs of analytic classification theorems and maximal-operator estimates for planar curve families. The theorem numbering follows [arXiv:2609.39217](https://arxiv.org/abs/2609.39217).

The family consists of graphs

$$
\Gamma_{z,u}=\{(t,\gamma(t,z,u)):t\in I\},
\qquad I=[a,b],\quad a<b,\quad (z,u)\in W\subset\mathbb R^2\times\mathbb R^d.
$$

The [result catalog](docs/RESULTS.md) gives the mathematical statements, hypotheses, and corresponding Lean declarations.

## Classification theorems

| Result | Statement and hypotheses |
|---|---|
| **Theorem 1.4** | For an open parameter domain and a defining function analytic near $I\times\overline W$, the family admits a Nikodym set exactly when it has massive curve reuse or local reuse not covered by countably many smooth foliations. |
| **Theorem 1.5** | For a nonempty bounded open parameter domain, an analytic defining function, and constant point and curve ranks, the four rank cases determine Nikodym existence, curve reuse, and foliation coverage. |
| **Proposition 1.6** | For the analytic parameter domains specified in the theorem, finitely many connected analytic families of constant ranks preserve Nikodym existence and massive reuse. They also preserve uncovered local reuse when the original family has no massive reuse. The time interval is preserved and the auxiliary dimension does not increase. |
| **Corollary 1.2** | A smooth cinematic family on an open parameter domain admits no Nikodym set, in every auxiliary dimension $d\ge0$. |

Public declarations: `theorem_1_4_proved`, `theorem_1_5_proved`, `proposition_1_6_paper_proved`, and `corollary_1_2_smooth`.

## Maximal estimates and local smoothing

For an open parameter domain, a smooth defining function on the original closed time interval, and a compact parameter set $K\subset W$, assume cinematic nondegeneracy on $I\times K$. The original interval maximal operator has a bounded Lipschitz $L^p\to L^p$ realization in these finite-exponent ranges:

| Dimension | Exponent | Lean declaration |
|---|---|---|
| $d=1$ | $2<p<\infty$ | `Family.theorem_1_1_one_auxiliary_proved` |
| Every $d\ge0$ | $(d+1)(d+2)\le p<\infty$ | `Family.theorem_1_1_high_p_proved` |

These realizations agree almost everywhere with the pointwise operator on continuous compactly supported functions. Closed-domain cinematic nondegeneracy is expressed using canonical within-domain jets.

**Theorem 2.1 and Corollary 2.2** give local smoothing and maximal frequency estimates for every $d\ge0$ and finite $p\ge(d+1)(d+2)$. For a globally smooth phase, a fixed sufficiently small neighborhood of a cinematic point, a real smooth compactly supported cutoff supported there, and $f\in L^1\cap L^p$, the frequency factors are respectively

$$
2^{(-(d+1)/p+\varepsilon)k}
\qquad\text{and}\qquad
2^{(-1/p+\varepsilon)k},\qquad \varepsilon>0.
$$

**Lemma 2.3** supplies the corresponding exact-scale decoupling theorem for smooth cinematic phases with a rapidly decaying $L^2$ error.

## Analytic structure results

The library also proves the analytic Wronskian criterion on nondegenerate bounded closed intervals (**Theorem 5.3**), analytic coefficient representation (**Lemma 5.6**), elimination of redundant parameters (**Lemma 6.1**), effective-dimension and center-slice reductions (**Corollaries 6.2–6.3**), and countable smooth tangent-field coverage (**Lemma 7.1**).

## Build and verify

The project pins Lean `v4.32.0-rc1` and Mathlib commit `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`.

With Git, Python 3, and the Lean toolchain manager available, run from the repository root:

```sh
lake exe cache get
bash scripts/check.sh
```

The check builds the library and audits the transitive axiom dependencies of its declarations. The allowed logical axioms are `propext`, `Classical.choice`, and `Quot.sound`. The [GitHub workflow](.github/workflows/lean.yml) runs the same check on pushes and pull requests.

Use the library through:

```lean
import PlanarNikodym
```

- [Precise theorem statements and Lean declarations](docs/RESULTS.md)
- [Build, verification, and maintenance](docs/BUILD.md)
- [Source module index](docs/MODULE_INDEX.md)
- [Verification procedure](verification/README.md)
