import PlanarNikodym.Analysis.Fourier.GlyzConicGeometry
import PlanarNikodym.Analysis.Fourier.GlyzFourierPartition

/-! Finite radial localization of actual cone-supported Schwartz pieces.
The partition and its operator bounds depend on the fixed frequency
range and radial width, and are chosen before the curve and angular depth. -/
noncomputable section
open Set Metric MeasureTheory
open scoped FourierTransform BigOperators NNReal ENNReal
namespace PlanarNikodym

def glyzConeBox (k : ℕ) (γ : ℝ → GlyzSpace k) (s δ R rmin rmax : ℝ) :
    Set (GlyzConeSpace k) :=
  {z | ∃ r ∈ Icc rmin rmax, ∃ ξ ∈ glyzEnlargedCurveBox γ k s δ R,
    z = WithLp.toLp 2 (r • ξ, r)}

def glyzConeFrequencyRange (k : ℕ) (H rmin rmax : ℝ) : Set (GlyzConeSpace k) :=
  (WithLp.toLp 2) '' (closedBall (0 : GlyzSpace k) H ×ˢ Icc rmin rmax)

theorem isCompact_glyzConeFrequencyRange (k : ℕ) (H rmin rmax : ℝ) :
    IsCompact (glyzConeFrequencyRange k H rmin rmax) :=
  ((isCompact_closedBall _ _).prod isCompact_Icc).image
    (WithLp.prodContinuousLinearEquiv 2 ℝ (GlyzSpace k) ℝ).symm.continuous

theorem glyzEnlargedCurveBox_norm_le {k : ℕ} (γ : ℝ → GlyzSpace k)
    {s δ R B : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R) (_hB : 0 ≤ B)
    (hder : ∀ j ≤ k, ‖iteratedDeriv j γ s‖ ≤ B)
    {ξ : GlyzSpace k} (hξ : ξ ∈ glyzEnlargedCurveBox γ k s δ R) :
    ‖ξ‖ ≤ B + (k : ℝ) * R * B := by
  obtain ⟨v, hv, rfl⟩ := hξ
  have hγ : ‖γ s‖ ≤ B := by simpa only [iteratedDeriv_zero] using hder 0 (Nat.zero_le _)
  unfold glyzCurveBoxPoint
  calc
    _ ≤ ‖γ s‖ + ‖∑ j : Fin k, (δ ^ ((j : ℕ) + 1) * v j) •
        iteratedDeriv ((j : ℕ) + 1) γ s‖ := norm_add_le _ _
    _ ≤ B + ∑ j : Fin k, ‖(δ ^ ((j : ℕ) + 1) * v j) •
        iteratedDeriv ((j : ℕ) + 1) γ s‖ := add_le_add hγ (norm_sum_le _ _)
    _ ≤ B + ∑ _j : Fin k, R * B := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ _)]
      apply mul_le_mul _ (hder _ (by omega)) (norm_nonneg _) hR
      exact (mul_le_mul (pow_le_one₀ hδ hδ1) (hv j) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul R)
    _ = _ := by simp; ring

theorem glyzConeBox_subset_frequencyRange {k : ℕ} (γ : ℝ → GlyzSpace k)
    {s δ R B rmin rmax : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hR : 0 ≤ R) (hB : 0 ≤ B) (hrmin : 0 ≤ rmin)
    (hder : ∀ j ≤ k, ‖iteratedDeriv j γ s‖ ≤ B) :
    glyzConeBox k γ s δ R rmin rmax ⊆
      glyzConeFrequencyRange k (rmax * (B + (k : ℝ) * R * B)) rmin rmax := by
  rintro z ⟨r, hr, ξ, hξ, rfl⟩
  refine ⟨(r • ξ, r), ⟨?_, hr⟩, rfl⟩
  simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (hrmin.trans hr.1)]
  exact mul_le_mul hr.2 (glyzEnlargedCurveBox_norm_le γ hδ hδ1 hR hB hder hξ)
    (norm_nonneg _) (hrmin.trans (hr.1.trans hr.2))

theorem exists_glyz_cone_radial_partition (k : ℕ) (H : ℝ)
    {rmin rmax σ : ℝ} (hrmin : 0 < rmin) (hσ : 0 < σ) :
    ∃ (S : Finset (Icc rmin rmax)) (χ : S → SchwartzMap (GlyzConeSpace k) ℂ)
      (M : ℝ), 0 < M ∧
      (∀ i, Function.support (χ i) ⊆
        {z | |(WithLp.ofLp z).2 / ((i : Icc rmin rmax) : ℝ) - 1| < σ}) ∧
      (∀ f : SchwartzMap (GlyzConeSpace k) ℂ,
        Function.support (𝓕 (f : GlyzConeSpace k → ℂ)) ⊆
          glyzConeFrequencyRange k H rmin rmax →
        ∑ i : S, glyzFourierProjector (χ i) f = f) ∧
      (∀ (p : ℝ≥0), 1 ≤ p → ∀ (i : S) (f : SchwartzMap (GlyzConeSpace k) ℂ),
        lpNorm (glyzFourierProjector (χ i) f : GlyzConeSpace k → ℂ) p volume ≤
          M * lpNorm (f : GlyzConeSpace k → ℂ) p volume) := by
  let U : Icc rmin rmax → Set (GlyzConeSpace k) := fun a =>
    {z | |(WithLp.ofLp z).2 / (a : ℝ) - 1| < σ}
  have hU (a : Icc rmin rmax) : IsOpen (U a) := by
    apply isOpen_lt _ continuous_const
    exact (((continuous_snd.comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ (GlyzSpace k) ℝ).continuous).div_const _).sub
        continuous_const).abs
  have hcover : glyzConeFrequencyRange k H rmin rmax ⊆ ⋃ a, U a := by
    rintro z ⟨⟨ξ, r⟩, ⟨_, hr⟩, rfl⟩
    apply mem_iUnion.mpr
    refine ⟨⟨r, hr⟩, ?_⟩
    change |r / r - 1| < σ
    simpa only [div_self (ne_of_gt (hrmin.trans_le hr.1)), sub_self, abs_zero] using hσ
  obtain ⟨S, χ, M, hM, hχ, _, hsum, hbound⟩ := exists_glyz_finite_fourier_partition
    (glyzConeFrequencyRange k H rmin rmax)
    (isCompact_glyzConeFrequencyRange k H rmin rmax) U hU hcover
  exact ⟨S, χ, M, hM, hχ, hsum, hbound⟩

end PlanarNikodym
