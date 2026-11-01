import PlanarNikodym.Geometry.AnalyticOrderedSimpleRoots
import PlanarNikodym.Geometry.WeierstrassRootBounds
import PlanarNikodym.Geometry.WeierstrassDiscriminant

/-! Complete analytic branches of all real roots of a monic polynomial family
near a simple-root coefficient vector. A uniform Cauchy bound prevents roots
from entering from infinity. -/

noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluation of the actual polynomial is jointly analytic in parameter and root variable. -/
theorem analyticAt_joint_weierstrassPolynomial_eval
    {m : ℕ} (a : E → Fin m → ℝ) (x₀ : E) (t₀ : ℝ)
    (ha : AnalyticAt ℝ a x₀) :
    AnalyticAt ℝ (fun z : E × ℝ => (weierstrassPolynomial (a z.1)).eval z.2)
      (x₀, t₀) := by
  simp only [weierstrassPolynomial_eval]
  apply (analyticAt_snd.pow m).add
  apply Finset.analyticAt_fun_sum
  intro i _
  have hai : AnalyticAt ℝ (fun z : E × ℝ => a z.1 i) (x₀, t₀) :=
    AnalyticAt.comp (x := (x₀, t₀)) (f := fun z : E × ℝ => z.1)
      (g := fun x => a x i) (analyticAt_pi_iff.mp ha i) analyticAt_fst
  exact hai.mul (analyticAt_snd.pow (i : ℕ))

variable [CompleteSpace E]

/-- A monic analytic polynomial family whose base real roots are simple has a complete
finite strictly ordered analytic root atlas over the entire real axis. The radius bound
and common parameter ball are chosen before all neighboring parameters and roots. -/
theorem exists_ordered_analytic_polynomial_root_branches
    {m : ℕ} (a : E → Fin m → ℝ) (x₀ : E) (ha : AnalyticAt ℝ a x₀)
    (hsimple : ∀ t : ℝ, (weierstrassPolynomial (a x₀)).eval t = 0 →
      deriv (fun s => (weierstrassPolynomial (a x₀)).eval s) t ≠ 0) :
    ∃ (n : ℕ) (ε R : ℝ), 0 < ε ∧ 0 < R ∧ ∃ ρ : Fin n → E → ℝ,
      AnalyticOnNhd ℝ a (Metric.ball x₀ ε) ∧
      (∀ i, AnalyticOnNhd ℝ (ρ i) (Metric.ball x₀ ε)) ∧
      (∀ x ∈ Metric.ball x₀ ε, StrictMono (fun i => ρ i x)) ∧
      (∀ x ∈ Metric.ball x₀ ε, ∀ i, ρ i x ∈ Ioo (-R) R) ∧
      ∀ x ∈ Metric.ball x₀ ε, ∀ t : ℝ,
        (weierstrassPolynomial (a x)).eval t = 0 ↔ ∃ i, t = ρ i x := by
  obtain ⟨W, R, hW, hxW, hR, hbound⟩ :=
    exists_open_nhds_uniform_weierstrass_root_bound a x₀ ha.continuousAt
  let f : E × ℝ → ℝ := fun z => (weierstrassPolynomial (a z.1)).eval z.2
  have hf (t : ℝ) (_ht : t ∈ Icc (-R) R) : AnalyticAt ℝ f (x₀, t) :=
    analyticAt_joint_weierstrassPolynomial_eval a x₀ t ha
  have hleft : f (x₀, -R) ≠ 0 := by
    intro hz
    have h := hbound x₀ hxW (-R) hz
    simp [abs_neg, abs_of_pos hR] at h
  have hright : f (x₀, R) ≠ 0 := by
    intro hz
    have h := hbound x₀ hxW R hz
    simp [abs_of_pos hR] at h
  obtain ⟨n, ε₀, hε₀, ρ, hρ, hmono, hI, hroots⟩ :=
    exists_ordered_analytic_simple_root_branches f x₀ (-R) R (by linarith)
      hf hleft hright (fun t _ ht => hsimple t ht)
  have hnear : {x | x ∈ W ∧ x ∈ Metric.ball x₀ ε₀ ∧ AnalyticAt ℝ a x} ∈ 𝓝 x₀ := by
    filter_upwards [hW.mem_nhds hxW, Metric.ball_mem_nhds x₀ hε₀,
      ha.eventually_analyticAt] with x hxW hxB hxa
    exact ⟨hxW, hxB, hxa⟩
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨n, ε, R, hε, hR, ρ, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hb hx).2.2
  · intro i x hx
    exact hρ i x (hb hx).2.1
  · intro x hx
    exact hmono x (hb hx).2.1
  · intro x hx i
    exact hI x (hb hx).2.1 i
  · intro x hx t
    constructor
    · intro ht
      have htI : t ∈ Ioo (-R) R := abs_lt.mp (hbound x (hb hx).1 t ht)
      exact (hroots x (hb hx).2.1 t htI).mp ht
    · rintro ⟨i, rfl⟩
      exact (hroots x (hb hx).2.1 (ρ i x) (hI x (hb hx).2.1 i)).mpr ⟨i, rfl⟩

/-- Nonvanishing of the actual Sylvester collision determinant supplies the simple-root
hypothesis; no root list, root bound, or covering is included among the assumptions. -/
theorem exists_ordered_analytic_polynomial_root_branches_of_collisionDet_ne_zero
    {m : ℕ} (a : E → Fin m → ℝ) (x₀ : E) (ha : AnalyticAt ℝ a x₀)
    (hdet : weierstrassCollisionDet (a x₀) ≠ 0) :
    ∃ (n : ℕ) (ε R : ℝ), 0 < ε ∧ 0 < R ∧ ∃ ρ : Fin n → E → ℝ,
      AnalyticOnNhd ℝ a (Metric.ball x₀ ε) ∧
      (∀ i, AnalyticOnNhd ℝ (ρ i) (Metric.ball x₀ ε)) ∧
      (∀ x ∈ Metric.ball x₀ ε, StrictMono (fun i => ρ i x)) ∧
      (∀ x ∈ Metric.ball x₀ ε, ∀ i, ρ i x ∈ Ioo (-R) R) ∧
      ∀ x ∈ Metric.ball x₀ ε, ∀ t : ℝ,
        (weierstrassPolynomial (a x)).eval t = 0 ↔ ∃ i, t = ρ i x :=
  exists_ordered_analytic_polynomial_root_branches a x₀ ha
    (deriv_ne_zero_of_weierstrassCollisionDet_ne_zero (a x₀) hdet)

end PlanarNikodym
