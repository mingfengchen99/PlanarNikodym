import PlanarNikodym.Analysis.Localization.AnalyticCutoff

/-! Actual finite smooth localization of a compactly supported cutoff,
subordinate to any open cover of its support. -/
noncomputable section
open Set
open scoped ContDiff Manifold

namespace PlanarNikodym

/-- A nonnegative smooth compact cutoff is an exact finite sum of smooth
compact cutoffs supported in the prescribed open patches. -/
theorem exists_finite_cutoff_partition
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (hcover : tsupport χ ⊆ ⋃ i, U i) :
    ∃ (S : Finset ι) (ψ : S → E → ℝ),
      (∀ i, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧
        tsupport (ψ i) ⊆ tsupport χ ∧ tsupport (ψ i) ⊆ U i ∧
        ∀ x, 0 ≤ ψ i x ∧ ψ i x ≤ χ x) ∧
      ∀ x, ∑ i : S, ψ i x = χ x := by
  classical
  obtain ⟨S, hS⟩ := hc.isCompact.elim_finite_subcover U hU hcover
  have hcoverS : tsupport χ ⊆ ⋃ i : S, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hS hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ, E)) (isClosed_tsupport χ) (fun i : S => U i) (fun i => hU i) hcoverS
  let ψ : S → E → ℝ := fun i x => χ x * ρ i x
  refine ⟨S, ψ, ?_, ?_⟩
  · intro i
    refine ⟨hχ.mul (ρ i).contMDiff.contDiff, hc.mul_right,
      tsupport_mul_subset_left, tsupport_mul_subset_right.trans (hρ i), ?_⟩
    intro x
    exact ⟨mul_nonneg (hχ0 x) (ρ.nonneg i x),
      (mul_le_mul_of_nonneg_left (ρ.le_one i x) (hχ0 x)).trans_eq (mul_one _)⟩
  · intro x
    by_cases hx : x ∈ tsupport χ
    · have hsum : ∑ i : S, ρ i x = 1 :=
        ρ.sum_finsupport' x hx (Finset.subset_univ _)
      change (∑ i : S, χ x * ρ i x) = χ x
      rw [← Finset.mul_sum, hsum, mul_one]
    · have hz := image_eq_zero_of_notMem_tsupport hx
      simp only [ψ, hz, zero_mul, Finset.sum_const_zero]

end PlanarNikodym
