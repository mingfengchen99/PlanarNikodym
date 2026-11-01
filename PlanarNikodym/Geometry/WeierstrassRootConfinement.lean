import PlanarNikodym.Geometry.ContinuousPolynomialJets
import PlanarNikodym.Geometry.CompactFiberNeighborhood

/-! Roots of a monic family whose lower coefficients vanish at the base point
are confined to any prescribed small interval on one actual base neighborhood. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

/-- The distinguished polynomial is t^m; continuity and compact exclusion
confine every nearby real root, including multiple roots and degree zero. -/
theorem exists_open_nhds_weierstrass_roots_small
    {E : Type*} [TopologicalSpace E] {m : ℕ} (a : E → Fin m → ℝ) (x₀ : E)
    (ha : ContinuousAt a x₀) (ha0 : a x₀ = 0) (r : ℝ) (hr : 0 < r) :
    ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧
      ∀ x ∈ U, ∀ t : ℝ, (weierstrassPolynomial (a x)).eval t = 0 → |t| < r := by
  obtain ⟨W, R, hW, hxW, _, hbound⟩ :=
    exists_open_nhds_uniform_weierstrass_root_bound a x₀ ha
  let K := Icc (-R) R ∩ {t : ℝ | r ≤ |t|}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hp (t : ℝ) (ht : t ∈ K) :
      ∀ᶠ z : E × ℝ in 𝓝 (x₀, t), (weierstrassPolynomial (a z.1)).eval z.2 ≠ 0 := by
    have ht0 : t ≠ 0 := by
      intro hz
      have hrt : r ≤ |t| := ht.2
      rw [hz, abs_zero] at hrt
      linarith
    have hn : (weierstrassPolynomial (a x₀)).eval t ≠ 0 := by
      simpa only [weierstrassPolynomial_eval, ha0, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero, add_zero] using pow_ne_zero m ht0
    have hc := continuousAt_joint_weierstrassPolynomial_iterate_derivative_eval a x₀ t ha 0
    simp only [Function.iterate_zero_apply] at hc
    exact hc.eventually_ne hn
  obtain ⟨V, hV, hxV, htest⟩ := exists_open_nhds_compact_fiber_property
    (fun z : E × ℝ => (weierstrassPolynomial (a z.1)).eval z.2 ≠ 0) x₀ K hK hp
  refine ⟨W ∩ V, hW.inter hV, ⟨hxW, hxV⟩, ?_⟩
  intro x hx t ht
  by_contra! hn
  have hb := abs_lt.mp (hbound x hx.1 t ht)
  exact htest x hx.2 t ⟨⟨hb.1.le, hb.2.le⟩, hn⟩ ht

end PlanarNikodym
