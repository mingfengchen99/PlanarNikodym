import PlanarNikodym.Analysis.Localization.FiniteCutoffPartition

/-! Actual finite smooth partition of a complex amplitude, retaining
compact support and an exact pointwise sum. -/
noncomputable section
open Set
open scoped ContDiff Manifold
namespace PlanarNikodym

theorem e2_exists_complex_amplitude_partition
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] {a : E → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) (hcover : tsupport a ⊆ ⋃ i, U i) :
    ∃ b : ι → E → ℂ,
      (∀ i, ContDiff ℝ ∞ (b i) ∧ HasCompactSupport (b i) ∧ tsupport (b i) ⊆ U i) ∧
      ∀ z, ∑ i : ι, b i z = a z := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ, E)) (isClosed_tsupport a) U hU hcover
  let b : ι → E → ℂ := fun i z => (ρ i z : ℝ) • a z
  have hreal (i : ι) : ContDiff ℝ ∞ (fun z : E => (ρ i z : ℝ)) :=
    (ρ i).contMDiff.contDiff
  have hb (i : ι) : ContDiff ℝ ∞ (b i) := (hreal i).smul ha
  have hbc (i : ι) : HasCompactSupport (b i) := by
    exact hc.smul_left (f := fun z : E => (ρ i z : ℝ))
  have hbs (i : ι) : tsupport (b i) ⊆ U i :=
    (tsupport_smul_subset_left (fun z : E => (ρ i z : ℝ)) a).trans (hρ i)
  refine ⟨b, fun i => ⟨hb i, hbc i, hbs i⟩, ?_⟩
  intro z
  by_cases hz : a z = 0
  · simp only [b, hz, smul_zero, Finset.sum_const_zero]
  have hh : (∑ i : ι, (ρ i z : ℝ)) = 1 :=
    ρ.sum_finsupport' z (subset_tsupport a hz) (Finset.subset_univ _)
  calc
    (∑ i : ι, b i z) = (∑ i : ι, (ρ i z : ℝ)) • a z := by
      exact (Finset.sum_smul (s := Finset.univ) (f := fun i : ι => (ρ i z : ℝ)) (x := a z)).symm
    _ = a z := by rw [hh, one_smul]

end PlanarNikodym
