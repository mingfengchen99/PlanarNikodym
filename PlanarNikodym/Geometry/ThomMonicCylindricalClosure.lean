import PlanarNikodym.Geometry.ThomCylindricalClosureCore
import PlanarNikodym.Geometry.ContinuousPolynomialJets

/-! The actual higher-dimensional Thom closure formula for a finite family
of fixed scalar multiples of monic continuous coefficient families. In
particular no compact section, constant root count, or root branch is input. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym

theorem exists_local_compact_polynomial_sign_sections
    {E ι : Type*} [TopologicalSpace E] [Fintype ι]
    (C V : Set E) (P : E → ι → ℝ[X]) (s : ι → Fin 3)
    (m : ι → ℕ) (a : ∀ j, E → Fin (m j) → ℝ) (c : ι → ℝ)
    (hV : IsOpen V) (ha : ∀ j, ContinuousOn (a j) V)
    (hnorm : ∀ x ∈ V, ∀ j, P x j = Polynomial.C (c j) * weierstrassPolynomial (a j x))
    (hne : ∀ x ∈ C, (polynomialThomFamilyCell false (P x) s).Nonempty)
    (x : E) (hx : x ∈ V) :
    ∃ (U : Set E) (R : ℝ), IsOpen U ∧ x ∈ U ∧ 0 < R ∧
      ∀ y ∈ C ∩ (U ∩ V), ∃ t ∈ Icc (-R) R,
        t ∈ polynomialThomFamilyCell false (P y) s := by
  classical
  choose U R hU hxU hR hroots using fun j =>
    exists_open_nhds_uniform_weierstrass_root_bound (a j) x
      ((ha j x hx).continuousAt (hV.mem_nhds hx))
  let R₀ : ℝ := 1 + ∑ j, |R j|
  have hsum : 0 ≤ ∑ j, |R j| := Finset.sum_nonneg (fun j _ => abs_nonneg (R j))
  have hR₀ : 0 < R₀ := by dsimp [R₀]; linarith
  have hRR (j : ι) : R j < R₀ := by
    have hle : |R j| ≤ ∑ k, |R k| :=
      Finset.single_le_sum (fun k _ => abs_nonneg (R k)) (Finset.mem_univ j)
    have hj := le_abs_self (R j)
    dsimp [R₀]
    linarith
  refine ⟨⋂ j, U j, R₀ + 1, isOpen_iInter_of_finite hU,
    mem_iInter.mpr hxU, by linarith, ?_⟩
  intro y hy
  apply polynomial_sign_cell_exists_bounded_point (P y) s R₀ hR₀ ?_ (hne y hy.1)
  intro j hj t ht
  have hc : c j ≠ 0 := by
    intro he
    apply hj
    rw [hnorm y hy.2.2 j, he]
    simp
  have ht' : (weierstrassPolynomial (a j y)).eval t = 0 := by
    rw [hnorm y hy.2.2 j, eval_mul, eval_C] at ht
    exact (mul_eq_zero.mp ht).resolve_left hc
  exact (hroots j y (mem_iInter.mp hy.2.1 j) t ht').trans (hRR j)

/-- Fixed-degree monic normalization constructs every extra hypothesis of
the compact-section closure core from the original coefficient continuity.
The constants may be zero, which includes the literal zero tail in a
derivative-closed family. -/
theorem polynomialThomCylinder_closure_of_monic_normalization
    {E ι : Type*} [TopologicalSpace E] [Fintype ι]
    (C V : Set E) (P : E → ι → ℝ[X]) (s : ι → Fin 3)
    (m : ι → ℕ) (a : ∀ j, E → Fin (m j) → ℝ) (c : ι → ℝ)
    (hV : IsOpen V) (hCV : C ⊆ V) (ha : ∀ j, ContinuousOn (a j) V)
    (hnorm : ∀ x ∈ V, ∀ j, P x j = Polynomial.C (c j) * weierstrassPolynomial (a j x))
    (hder : ∀ x ∈ V, ∀ j, ∃ k, (P x j).derivative = P x k)
    (hne : ∀ x ∈ C, (polynomialThomFamilyCell false (P x) s).Nonempty) :
    closure (polynomialThomCylinder C P s) ∩ (V ×ˢ univ) =
      {z | z.1 ∈ closure C ∩ V ∧ z.2 ∈ polynomialThomFamilyCell true (P z.1) s} := by
  have hcont (x : E) (hx : x ∈ V) (t : ℝ) (j : ι) :
      ContinuousAt (fun z : E × ℝ => (P z.1 j).eval z.2) (x, t) := by
    have hc : ContinuousAt (fun z : E × ℝ =>
        c j * (weierstrassPolynomial (a j z.1)).eval z.2) (x, t) := by
      apply continuousAt_const.mul
      simpa only [Function.iterate_zero_apply] using
        continuousAt_joint_weierstrassPolynomial_iterate_derivative_eval
          (a j) x t ((ha j x hx).continuousAt (hV.mem_nhds hx)) 0
    apply hc.congr
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hV.mem_nhds hx)] with z hz
    rw [hnorm z.1 hz j, eval_mul, eval_C]
  have hstable (j : ι) : (∀ x ∈ V, P x j = 0) ∨ (∀ x ∈ V, P x j ≠ 0) := by
    by_cases hc : c j = 0
    · left
      intro x hx
      rw [hnorm x hx j, hc]
      simp
    · right
      intro x hx
      rw [hnorm x hx j]
      exact mul_ne_zero (by simpa using hc) (weierstrassPolynomial_monic (a j x)).ne_zero
  apply polynomialThomCylinder_closure_of_compact_sections C V P s hV hCV hcont hder hstable hne
  intro x hx
  obtain ⟨U, R, hU, hxU, _, hsection⟩ :=
    exists_local_compact_polynomial_sign_sections C V P s m a c hV ha hnorm hne x hx.2
  refine ⟨U ∩ V, R, hU.inter hV, ⟨hxU, hx.2⟩, hsection⟩

end PlanarNikodym
