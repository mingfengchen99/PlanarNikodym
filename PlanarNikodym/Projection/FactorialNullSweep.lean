import PlanarNikodym.Projection.FactorialNullSlices
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Nat ENNReal
namespace PlanarNikodym.Wisewell

theorem boundedFactorialSweep_section (M : ℝ) (f : ℝ × Plane → ℝ)
    (K : Set ℝ) (t : ℝ) (ht : t ∈ K) :
    Prod.mk t ⁻¹' boundedFactorialSweep M f K =
      (fun p => f (t, p)) '' boundedFactorialGraph M := by
  ext y
  constructor
  · rintro ⟨⟨u, p⟩, ⟨hu, hp⟩, he⟩
    have htime : u = t := congrArg Prod.fst he
    subst u
    exact ⟨p, hp, congrArg Prod.snd he⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(t, p), ⟨ht, hp⟩, rfl⟩

theorem boundedFactorialSweep_section_of_not_mem (M : ℝ) (f : ℝ × Plane → ℝ)
    (K : Set ℝ) (t : ℝ) (ht : t ∉ K) :
    Prod.mk t ⁻¹' boundedFactorialSweep M f K = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨⟨u, p⟩, ⟨hu, _⟩, he⟩ := hy
  have htime : u = t := congrArg Prod.fst he
  exact ht (htime ▸ hu)

/-- The concrete symbolic sweep is compact and has Lebesgue measure zero.
For each fixed time, nullity follows from the constructed factorial
cancellation; compactness supplies the joint measurability for Fubini. -/
theorem volume_boundedFactorialSweep_eq_zero (M : ℝ) (hM : 0 ≤ M)
    (f : ℝ × Plane → ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hcont : ContinuousOn f (K ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (-M) M)))
    (hf : ∀ t ∈ K, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-M) M,
      DifferentiableAt ℝ (fun q => f (t, q)) p)
    (hDf : ∀ t ∈ K, ContinuousOn (fderiv ℝ (fun q => f (t, q)))
      (Icc (0 : ℝ) 1 ×ˢ Icc (-M) M))
    (hβ : ∀ t ∈ K, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-M) M,
      fderiv ℝ (fun q => f (t, q)) p (0, 1) ≠ 0)
    (hslope : ∀ t ∈ K, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-M) M,
      |fderiv ℝ (fun q => f (t, q)) p (1, 0) /
        fderiv ℝ (fun q => f (t, q)) p (0, 1)| < M) :
    volume (boundedFactorialSweep M f K) = 0 := by
  have hcompact := isCompact_boundedFactorialSweep M hM f K hK
    (hcont.mono (Set.prod_mono Subset.rfl (boundedFactorialGraph_subset M hM)))
  change (volume.prod volume) (boundedFactorialSweep M f K) = 0
  apply Measure.measure_prod_null_of_ae_null hcompact.measurableSet
  apply Filter.Eventually.of_forall
  intro t
  change volume (Prod.mk t ⁻¹' boundedFactorialSweep M f K) = 0
  by_cases ht : t ∈ K
  · rw [boundedFactorialSweep_section M f K t ht]
    exact volume_image_boundedFactorialGraph_eq_zero M hM (fun q => f (t, q))
      (hf t ht) (hDf t ht) (hβ t ht) (hslope t ht)
  · rw [boundedFactorialSweep_section_of_not_mem M f K t ht, measure_empty]

/-- A local scalar family with a bounded cancellation slope admits an
actual Borel selector whose entire selected curves lie in a compact null
set. This is the bounded local form of Wisewell's construction. -/
theorem exists_compact_null_curves_of_bounded_slope (M : ℝ) (hM : 0 ≤ M)
    (f : ℝ × Plane → ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hcont : ContinuousOn f (K ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (-M) M)))
    (hf : ∀ t ∈ K, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-M) M,
      DifferentiableAt ℝ (fun q => f (t, q)) p)
    (hDf : ∀ t ∈ K, ContinuousOn (fderiv ℝ (fun q => f (t, q)))
      (Icc (0 : ℝ) 1 ×ˢ Icc (-M) M))
    (hβ : ∀ t ∈ K, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-M) M,
      fderiv ℝ (fun q => f (t, q)) p (0, 1) ≠ 0)
    (hslope : ∀ t ∈ K, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-M) M,
      |fderiv ℝ (fun q => f (t, q)) p (1, 0) /
        fderiv ℝ (fun q => f (t, q)) p (0, 1)| < M) :
    ∃ ψ : ℝ → ℝ, ∃ E : Set Plane,
      Measurable ψ ∧ (∀ y, ‖ψ y‖ ≤ M) ∧ IsCompact E ∧ volume E = 0 ∧
        ∀ y ∈ Icc (0 : ℝ) 1,
          (fun t => (t, f (t, (y, ψ y)))) '' K ⊆ E := by
  refine ⟨boundedFactorialChoice M, boundedFactorialSweep M f K,
    measurable_boundedFactorialChoice M hM, norm_boundedFactorialChoice_le M hM,
    isCompact_boundedFactorialSweep M hM f K hK
      (hcont.mono (Set.prod_mono Subset.rfl (boundedFactorialGraph_subset M hM))),
    volume_boundedFactorialSweep_eq_zero M hM f K hK hcont hf hDf hβ hslope, ?_⟩
  exact fun y hy => boundedFactorialChoice_curve_subset_sweep M y hy f K

end PlanarNikodym.Wisewell
