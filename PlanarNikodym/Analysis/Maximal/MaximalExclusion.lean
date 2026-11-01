import PlanarNikodym.Analysis.Maximal.Averaging
import PlanarNikodym.Geometry.OneParameterNull
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

/-- Chebyshev applied to the extended-valued pointwise supremum. -/
theorem Family.OpenMaximalEstimate.weak {d : ℕ} {G : Family 2 d}
    {U : Set (Parameters 2 d)} (h : G.OpenMaximalEstimate U) (a : ℝ≥0) (ha : a ≠ 0) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ O : Set Plane, IsOpen O → volume O < ∞ →
      volume {z | (a : ℝ≥0∞) ≤ G.positiveMaximal U (O.indicator (fun _ => 1)) z} ≤
        K * volume O := by
  obtain ⟨p, hp, C, hC⟩ := h
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hp0)
  refine ⟨(a : ℝ≥0∞)⁻¹ ^ (p : ℝ) * (C : ℝ≥0∞) ^ (p : ℝ), by finiteness, ?_⟩
  intro O hO hOf
  obtain ⟨hm, hb⟩ := hC O hO hOf
  have hm' := hm.stronglyMeasurable.aestronglyMeasurable (μ := volume)
  have hcheb := meas_ge_le_mul_pow_eLpNorm_enorm (μ := volume)
    (p := (p : ℝ≥0∞)) (by exact_mod_cast hp0) ENNReal.coe_ne_top hm'
    (by exact_mod_cast ha : (a : ℝ≥0∞) ≠ 0) (by simp)
  simp only [enorm_eq_self, ENNReal.coe_toReal] at hcheb
  calc
    _ ≤ (a : ℝ≥0∞)⁻¹ ^ (p : ℝ) *
        eLpNorm (G.positiveMaximal U (O.indicator (fun _ => 1))) p volume ^ (p : ℝ) := hcheb
    _ ≤ (a : ℝ≥0∞)⁻¹ ^ (p : ℝ) *
        ((C : ℝ≥0∞) * volume O ^ (1 / (p : ℝ))) ^ (p : ℝ) := by gcongr
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hpR.le, ← ENNReal.rpow_mul]
      simp [one_div, inv_mul_cancel₀ hpR.ne', mul_assoc]

/-- Outer regularity is used on the plane set only. No measurability of
`S`, which may be a parameter projection, is required. -/
theorem outer_null_of_open_tests (E : Set Plane) (hE : volume E = 0)
    (S : Set (Base 2)) (K : ℝ≥0∞) (hK : K ≠ ∞)
    (h : ∀ O : Set Plane, E ⊆ O → IsOpen O → volume O < ∞ →
      volume S ≤ K * volume O) : volume S = 0 := by
  apply le_antisymm _ zero_le
  apply le_of_forall_gt
  intro r hr
  obtain ⟨ε, hε, hsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt hK hr.ne'
  obtain ⟨O, hEO, hO, hvol⟩ := E.exists_isOpen_lt_of_lt (μ := volume) ε
    (by simpa [hE] using (show (0 : ℝ≥0∞) < ε by exact_mod_cast hε))
  exact (h O hEO hO (hvol.trans ENNReal.coe_lt_top)).trans_lt
    ((mul_le_mul_right hvol.le K).trans_lt (by simpa [mul_comm] using hsmall))

theorem Family.OpenMaximalEstimate.incidence_null {d : ℕ} {G : Family 2 d}
    {U : Set (Parameters 2 d)} (h : G.OpenMaximalEstimate U)
    (hU : U ⊆ G.W) (hs : G.IsSmooth)
    (E : Set Plane) (_hE : MeasurableSet E) (hE0 : volume E = 0) :
    volume (G.timeIncidenceCenters U E) = 0 := by
  classical
  let B (n : {n : ℕ // 0 < n}) : Set (Base 2) :=
    {z | ∃ u, (z, u) ∈ U ∧ (n.val : ℝ≥0∞)⁻¹ ≤ volume (G.hitTimes (z, u) E)}
  have hB (n : {n : ℕ // 0 < n}) : volume (B n) = 0 := by
    let a : ℝ≥0 := (n.val : ℝ≥0)⁻¹
    have ha : a ≠ 0 := inv_ne_zero (by exact_mod_cast n.property.ne')
    obtain ⟨K, hK, hweak⟩ := h.weak a ha
    apply outer_null_of_open_tests E hE0 (B n) K hK
    intro O hEO hO hOf
    apply (measure_mono (t := {z | (a : ℝ≥0∞) ≤
      G.positiveMaximal U (O.indicator (fun _ => 1)) z}) ?_).trans (hweak O hO hOf)
    rintro z ⟨u, hu, ht⟩
    have hgraph : ContinuousOn (G.graphMap (z, u)) G.I.carrier :=
      continuousOn_id.prodMk (hs.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, hU hu⟩))
    have hm : MeasurableSet (G.hitTimes (z, u) O) := by
      exact measurableSet_inter_preimage_continuousOn G.I.carrier measurableSet_Icc
        (G.graphMap (z, u)) hgraph O hO.measurableSet
    have hhit : G.hitTimes (z, u) E ⊆ G.hitTimes (z, u) O :=
      fun t ht => ⟨ht.1, hEO ht.2⟩
    have hle := (ht.trans (measure_mono hhit)).trans
      ((G.positiveAverage_indicator (z, u) O hm).symm.le.trans
        (G.positiveAverage_le_maximal (O.indicator (fun _ => 1)) hu))
    simpa [a, ENNReal.coe_inv (show (n.val : ℝ≥0) ≠ 0 by
      exact_mod_cast n.property.ne')] using hle
  apply measure_mono_null (t := ⋃ n, B n) ?_ (measure_iUnion_null hB)
  rintro z ⟨u, hu, ht⟩
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt ht.ne'
  have hn0 : 0 < n := by
    by_contra hnot
    have : n = 0 := by omega
    simp [this] at hn
  exact mem_iUnion.mpr ⟨⟨n, hn0⟩, u, hu, hn.le⟩

theorem Family.OpenMaximalEstimate.no_nikodym {d : ℕ} {G : Family 2 d}
    (h : G.OpenMaximalEstimate G.W) (hs : G.IsSmooth) : ¬ G.AdmitsNikodym := by
  apply G.no_nikodym_of_incidence_null
  intro E hE hE0
  rw [← G.timeIncidenceCenters_eq hs G.W Subset.rfl E]
  exact h.incidence_null Subset.rfl hs E hE hE0

end PlanarNikodym
