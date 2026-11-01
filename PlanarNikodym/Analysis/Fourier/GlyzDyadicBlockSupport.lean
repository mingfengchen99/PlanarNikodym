import PlanarNikodym.Analysis.Fourier.GlyzDyadicOptimalRescaling
import PlanarNikodym.Analysis.Fourier.GlyzTaylorFrequencyImage
import PlanarNikodym.Analysis.Fourier.GlyzTransverseCoordinates
import PlanarNikodym.Analysis.Fourier.GlyzPolarBilinearMeasure

/-! Actual support of a dyadic block sum in one uniformly enlarged
parent moment box, with a constant depending only on dimension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped FourierTransform NNReal ENNReal
namespace PlanarNikodym

theorem glyzMomentFrequencyBox_affine_image_radius (m : ℕ) (c κ s δ R : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) :
    (fun ξ => (EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m c) +
      glyzMomentAffineEuclidean m c κ hκ.ne' ξ) ''
      glyzFrequencyBox (glyzMomentFrequencyFrame m s δ hδ)
        ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m s)) R =
    glyzFrequencyBox (glyzMomentFrequencyFrame m (c + κ * s) (κ * δ) (mul_pos hκ hδ))
      ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m (c + κ * s))) R := by
  rw [glyzFrequencyBox_eq_image, glyzFrequencyBox_eq_image, ← Set.image_comp]
  apply congrArg (fun f : Base m → GlyzSpace m => f '' closedBall 0 R)
  funext v
  have hf := congrArg (fun T : GlyzSpace m →L[ℝ] GlyzSpace m =>
    T ((EuclideanSpace.equiv (Fin m) ℝ).symm v))
    (glyzMomentFrequencyFrame_affine m c κ s δ hκ hδ)
  change glyzMomentAffineEuclidean m c κ hκ.ne'
      (glyzMomentFrequencyFrame m s δ hδ ((EuclideanSpace.equiv (Fin m) ℝ).symm v)) =
    glyzMomentFrequencyFrame m (c + κ * s) (κ * δ) (mul_pos hκ hδ)
      ((EuclideanSpace.equiv (Fin m) ℝ).symm v) at hf
  change _ + glyzMomentAffineEuclidean m c κ hκ.ne' (_ + _) = _ + _
  rw [map_add, hf, glyzMomentAffineEuclidean_curve m c κ s hκ.ne']
  abel

theorem exists_uniform_glyzMomentFrequencyBox_normalized (m : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
      glyzMomentFrequencyBox m s δ hδ ⊆
        glyzFrequencyBox (glyzMomentFrequencyFrame m 0 1 zero_lt_one)
          ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m 0)) R := by
  let Q := (glyzMomentFrequencyFrame m 0 1 zero_lt_one).symm.trans
    (EuclideanSpace.equiv (Fin m) ℝ)
  let H : (ℝ × ℝ) × Base m → Base m := fun z =>
    Q (((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m z.1.1) +
      ∑ j : Fin m, (z.1.2 ^ ((j : ℕ) + 1) * z.2 j) • glyzEuclideanJetBlock m m z.1.1 j) -
        (EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m 0))
  have hc : Continuous H := by
    apply Q.continuous.comp
    apply Continuous.sub _ continuous_const
    apply Continuous.add
    · apply (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp
      exact continuous_pi fun j => (continuous_fst.fst).pow _
    · apply continuous_finsetSum
      intro j _
      exact (((continuous_fst.snd).pow _).mul
        ((show Continuous (fun v : Base m => v j) from continuous_apply j).comp continuous_snd)).smul
        ((continuous_glyzEuclideanJetBlock m m j).comp continuous_fst.fst)
  have hk : IsCompact (((Icc (-1 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) ×ˢ closedBall (0 : Base m) 1) :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hk.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|C| + 1, by positivity, fun s hs δ hδ hδ1 ξ hξ => ?_⟩
  rw [glyzMomentFrequencyBox_eq_generators] at hξ
  obtain ⟨v, hv, rfl⟩ := hξ
  have hv' : v ∈ closedBall (0 : Base m) 1 := by
    simpa only [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one,
      Real.norm_eq_abs, mem_setOf_eq] using hv
  have h := hC ((s, δ), v) ⟨⟨hs, ⟨hδ.le, hδ1⟩⟩, hv'⟩
  exact h.trans (by linarith [le_abs_self C])

theorem exists_uniform_glyzMomentFrequencyBox_nested (m : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ (c κ s ρ : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ),
      s ∈ Icc (-1 : ℝ) 1 → ρ ≤ 1 →
      glyzMomentFrequencyBox m (c + κ * s) (κ * ρ) (mul_pos hκ hρ) ⊆
        glyzFrequencyBox (glyzMomentFrequencyFrame m c κ hκ)
          ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m c)) R := by
  obtain ⟨R, hR, h⟩ := exists_uniform_glyzMomentFrequencyBox_normalized m
  refine ⟨R, hR, fun c κ s ρ hκ hρ hs hρ1 => ?_⟩
  have hp := glyzMomentFrequencyBox_affine_image_radius m c κ 0 1 R hκ zero_lt_one
  simp only [mul_zero, add_zero, mul_one] at hp
  rw [← glyzMomentFrequencyBox_affine_image m c κ s ρ hκ hρ, ← hp]
  exact Set.image_mono (h s hs ρ hρ hρ1)

theorem exists_uniform_glyz_dyadic_descendant_box (m : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ n q i j : ℕ, j < 2 ^ q →
      glyzMomentFrequencyBox m (glyzDyadicCenter (n + q) (i * 2 ^ q + j))
        (glyzDyadicScale (n + q)) (glyzDyadicScale_pos (n + q)) ⊆
      glyzFrequencyBox (glyzMomentFrequencyFrame m (glyzDyadicCenter n i) (glyzDyadicScale n)
        (glyzDyadicScale_pos n))
        ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m (glyzDyadicCenter n i))) R := by
  obtain ⟨R, hR, h⟩ := exists_uniform_glyzMomentFrequencyBox_nested m
  refine ⟨R, hR, fun n q i j hj => ?_⟩
  have hc : glyzDyadicCenter n i + glyzDyadicScale n * (glyzDyadicCenter q j - 1 / 2) =
      glyzDyadicCenter (n + q) (i * 2 ^ q + j) := by
    rw [← glyzDyadicCenter_rescale]
    unfold glyzDyadicCenter
    ring
  have hjc := glyzDyadicCenter_mem_Icc hj
  have hs : glyzDyadicCenter q j - 1 / 2 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hjc.1, hjc.2]
  have hρ : glyzDyadicScale q ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have ht := h (glyzDyadicCenter n i) (glyzDyadicScale n) (glyzDyadicCenter q j - 1 / 2)
    (glyzDyadicScale q) (glyzDyadicScale_pos n) (glyzDyadicScale_pos q) hs hρ
  rw [hc] at ht
  convert ht using 1
  congr 1
  exact glyzDyadicScale_add n q

/-- One fixed enlarged parent box contains the Fourier support of every
actual dyadic block. In particular the uncertainty principle applies to
the block sum with a dimension-only constant. -/
theorem exists_uniform_glyz_dyadic_block_support (m : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ N n i : ℕ, n ≤ N → i < 2 ^ n →
      ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ, GlyzDyadicSupported m N f →
      Function.support (𝓕 ((glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ) :
        GlyzSpace m → ℂ)) ⊆
      glyzFrequencyBox (glyzMomentFrequencyFrame m (glyzDyadicCenter n i) (glyzDyadicScale n)
        (glyzDyadicScale_pos n))
        ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m (glyzDyadicCenter n i))) R := by
  classical
  obtain ⟨R, hR, h⟩ := exists_uniform_glyz_dyadic_descendant_box m
  refine ⟨R, hR, fun N n i hn hi f hf ξ hξ => ?_⟩
  by_contra hout
  have he : n + (N - n) = N := Nat.add_sub_of_le hn
  have hz (j : ℕ) (hj : j < 2 ^ (N - n)) :
      𝓕 (f (i * 2 ^ (N - n) + j) : GlyzSpace m → ℂ) ξ = 0 := by
    by_contra hjz
    apply hout
    apply h n (N - n) i j hj
    have hidx : i * 2 ^ (N - n) + j < 2 ^ N := by
      simpa only [he] using glyz_dyadic_descendant_lt hi hj
    convert hf _ (Finset.mem_range.mpr hidx) hjz using 1
    unfold glyzDyadicCenter glyzDyadicScale
    congr 1 <;> simp only [he]
  apply hξ
  change (𝓕 (∑ j ∈ Finset.range (2 ^ (N - n)), f (i * 2 ^ (N - n) + j) :
    SchwartzMap (GlyzSpace m) ℂ)) ξ = 0
  simp only [FourierTransform.fourier_sum, sum_apply]
  exact Finset.sum_eq_zero fun j hj => hz j (Finset.mem_range.mp hj)

theorem glyz_dyadic_block_uncertainty (m A : ℕ) {p : ℝ≥0} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ N n i : ℕ, n ≤ N → i < 2 ^ n →
      ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ, GlyzDyadicSupported m N f →
      ∀ x : GlyzSpace m,
        ‖(glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ) x‖ₑ ^ (p : ℝ) ≤
          ENNReal.ofReal C * glyzPowerAverage
            (glyzPolarMeasure A (glyzMomentFrequencyFrame m (glyzDyadicCenter n i)
              (glyzDyadicScale n) (glyzDyadicScale_pos n)))
            (glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ) p x := by
  obtain ⟨R, hR, hs⟩ := exists_uniform_glyz_dyadic_block_support m
  obtain ⟨C, hC, hu⟩ := glyz_uncertainty_fourier_box m A R hR hp
  refine ⟨C, hC, fun N n i hn hi f hf x => ?_⟩
  rw [glyzPolarMeasure_average]
  exact hu _ _ _ (hs N n i hn hi f hf) x

end PlanarNikodym
