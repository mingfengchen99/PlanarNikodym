import PlanarNikodym.Avoidance.SmoothFieldCover

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

/-- Lemma 7.1, strengthened to a finite exceptional time set for each curve.
Both derivatives in the hypotheses and conclusion are actual derivatives. -/
theorem lemma_7_1_finite_exceptions (I : Interval) (J : Set ℝ) (h : Plane → ℝ)
    (ha : AnalyticOnNhd ℝ h (I.carrier ×ˢ J))
    (hn : ∀ s ∈ J, ∃ t ∈ I.carrier, deriv (fun r => h (t, r)) s ≠ 0) :
    ∃ V : Family.Foliations, ∀ s ∈ J, ∃ Z : Set ℝ, Z.Finite ∧
      ∀ t ∈ I.carrier, t ∉ Z → ∃ i, V.field i (t, h (t, s)) ≠ 0 ∧
        Family.wedge (V.field i (t, h (t, s))) (1, deriv (fun r => h (r, s)) t) = 0 := by
  obtain ⟨V, hV⟩ := exists_countable_smooth_tangents h _ ha
  refine ⟨V, ?_⟩
  intro s hs
  let Z := {t | t ∈ I.carrier ∧ partialParameter h (t, s) = 0}
  have han : AnalyticOnNhd ℝ (fun t => partialParameter h (t, s)) I.carrier := by
    intro t ht
    exact (analyticAt_partialParameter (ha (t, s) ⟨ht, hs⟩)).comp
      (f := fun t : ℝ => (t, s)) (analyticAt_id.prod analyticAt_const)
  have hnon : ∃ t ∈ I.carrier, partialParameter h (t, s) ≠ 0 := by
    obtain ⟨t, ht, hd⟩ := hn s hs
    exact ⟨t, ht, by rwa [partialParameter_eq_deriv _ _ (ha _ ⟨ht, hs⟩).differentiableAt]⟩
  refine ⟨Z, analytic_zeros_finite_interval I _ han hnon, ?_⟩
  intro t ht htZ
  have hp : partialParameter h (t, s) ≠ 0 := fun h => htZ ⟨ht, h⟩
  obtain ⟨i, hi, he⟩ := hV (t, s) ⟨ht, hs⟩ hp
  exact ⟨i, hi, by rwa [partialTime_eq_deriv _ _ (ha _ ⟨ht, hs⟩).differentiableAt] at he⟩

theorem lemma_7_1 (I : Interval) (J : Set ℝ) (h : Plane → ℝ)
    (ha : AnalyticOnNhd ℝ h (I.carrier ×ˢ J))
    (hn : ∀ s ∈ J, ∃ t ∈ I.carrier, deriv (fun r => h (t, r)) s ≠ 0) :
    ∃ V : Family.Foliations, ∀ s ∈ J,
      ∀ᵐ t ∂volume.restrict I.carrier, ∃ i, V.field i (t, h (t, s)) ≠ 0 ∧
        Family.wedge (V.field i (t, h (t, s))) (1, deriv (fun r => h (r, s)) t) = 0 := by
  obtain ⟨V, hV⟩ := lemma_7_1_finite_exceptions I J h ha hn
  refine ⟨V, ?_⟩
  intro s hs
  obtain ⟨Z, hZ, hz⟩ := hV s hs
  have hnZ : ∀ᵐ t ∂volume.restrict I.carrier, t ∉ Z :=
    (compl_mem_ae_iff).mpr (hZ.countable.measure_zero _)
  filter_upwards [hnZ, ae_restrict_mem measurableSet_Icc] with t htZ ht
  exact hz t ht htZ

end PlanarNikodym
