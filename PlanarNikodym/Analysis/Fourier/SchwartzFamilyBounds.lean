import PlanarNikodym.Analysis.Fourier.FourierKernels
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! Uniform derivative estimates for functions supported in one compact set
give uniform Schwartz seminorm estimates. Continuous linear maps out of the
Schwartz space preserve arbitrary-order frequency decay, with one constant
for the whole parameter family. -/

noncomputable section
open Set
open scoped ContDiff FourierTransform

namespace PlanarNikodym

/-- Compact support turns a uniform full-derivative bound into a weighted
Schwartz seminorm bound, uniformly over an arbitrary parameter family. -/
theorem exists_uniform_schwartz_seminorm_bound
    {P E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : P → SchwartzMap E F) {K : Set E} (hK : IsCompact K)
    (hs : ∀ p, tsupport (S p) ⊆ K) (n k : ℕ) (B : P → ℝ) (hB : ∀ p, 0 ≤ B p)
    (hjet : ∀ p x, ‖iteratedFDeriv ℝ n (S p) x‖ ≤ B p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, SchwartzMap.seminorm ℝ k n (S p) ≤ C * B p := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn)
  let M : ℝ := max 1 R
  have hM : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  refine ⟨M ^ k, by positivity, fun p => ?_⟩
  apply SchwartzMap.seminorm_le_bound ℝ k n (S p) (mul_nonneg (by positivity) (hB p))
  intro x
  by_cases hx : x ∈ K
  · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) ((hR x hx).trans
      (le_max_right _ _)) k) (hjet p x) (norm_nonneg _) (by positivity)
  · have hz : iteratedFDeriv ℝ n (S p) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hs p (tsupport_iteratedFDeriv_subset n h)))
    simp only [hz, norm_zero, mul_zero]
    exact mul_nonneg (by positivity) (hB p)

/-- A continuous linear map to a normed space is controlled by finitely
many actual Schwartz seminorms. The finite set and constant are independent
of the Schwartz function. -/
theorem exists_schwartz_clm_finite_bound
    {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : SchwartzMap E F →L[ℝ] V) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ f, ‖T f‖ ≤ C * ∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 f := by
  let q : Seminorm ℝ (SchwartzMap E F) := (normSeminorm ℝ V).comp T.toLinearMap
  have hq : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ E F) q hq
  refine ⟨s, C, C.coe_nonneg, fun f => ?_⟩
  have hb : ‖T f‖ ≤ (C : ℝ) * s.sup (schwartzSeminormFamily ℝ E F) f := hC f
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  apply Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun i hi => apply_nonneg _ _)
  intro i hi
  exact Finset.single_le_sum (fun j hj => apply_nonneg (SchwartzMap.seminorm ℝ j.1 j.2) f) hi

/-- Rapid decay in every Schwartz seminorm implies rapid decay after any
continuous linear map to a normed space. No compactness of the parameter
set is assumed. -/
theorem exists_schwartz_clm_decay_constant
    {P E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : SchwartzMap E F →L[ℝ] V) (S : P → ℝ → SchwartzMap E F)
    (hdecay : ∀ k n N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p r, 1 ≤ r →
      SchwartzMap.seminorm ℝ k n (S p r) ≤ C * (r⁻¹) ^ N) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p r, 1 ≤ r → ‖T (S p r)‖ ≤ C * (r⁻¹) ^ N := by
  obtain ⟨s, C, hC, hb⟩ := exists_schwartz_clm_finite_bound T
  choose B hB hbound using fun i : ℕ × ℕ => hdecay i.1 i.2 N
  refine ⟨C * ∑ i ∈ s, B i, mul_nonneg hC (Finset.sum_nonneg fun i hi => hB i), ?_⟩
  intro p r hr
  calc
    _ ≤ C * ∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 (S p r) := hb _
    _ ≤ C * ∑ i ∈ s, B i * (r⁻¹) ^ N :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => hbound i p r hr) hC
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- A family with a fixed compact support and arbitrary-order decay of
every full derivative decays after any continuous linear Schwartz map.
The assumptions are actual derivative estimates, not an operator bound. -/
theorem exists_compact_schwartz_clm_decay_constant
    {P E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : SchwartzMap E F →L[ℝ] V) (S : P → ℝ → SchwartzMap E F)
    {K : Set E} (hK : IsCompact K) (hs : ∀ p r, tsupport (S p r) ⊆ K)
    (hdecay : ∀ n N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p r, 1 ≤ r →
      ∀ x, ‖iteratedFDeriv ℝ n (S p r) x‖ ≤ C * (r⁻¹) ^ N) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p r, 1 ≤ r → ‖T (S p r)‖ ≤ C * (r⁻¹) ^ N := by
  apply exists_schwartz_clm_decay_constant T S _ N
  intro k n M
  obtain ⟨B, hB, hb⟩ := hdecay n M
  let Q := P × {r : ℝ // 1 ≤ r}
  let S' : Q → SchwartzMap E F := fun y => S y.1 y.2.1
  let B' : Q → ℝ := fun y => B * (y.2.1⁻¹) ^ M
  obtain ⟨C, hC, hc⟩ := exists_uniform_schwartz_seminorm_bound S' hK
    (fun y => hs y.1 y.2.1) n k B' (fun y =>
      mul_nonneg hB (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans y.2.2)) M))
    (fun y x => hb y.1 y.2.1 y.2.2 x)
  refine ⟨C * B, mul_nonneg hC hB, ?_⟩
  intro p r hr
  simpa only [S', B', mul_assoc] using hc (p, ⟨r, hr⟩)

end PlanarNikodym
