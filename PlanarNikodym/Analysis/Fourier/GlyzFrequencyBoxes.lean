import PlanarNikodym.Analysis.Fourier.GlyzUncertainty
import PlanarNikodym.Analysis.Fourier.GlyzDecayWeights
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Actual affine Fourier parallelepipeds and their polar boxes. The
pointwise uncertainty constant is uniform over every frame and center. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory FourierTransform
open scoped FourierTransform ENNReal NNReal
namespace PlanarNikodym

abbrev GlyzSpace (m : ℕ) := EuclideanSpace ℝ (Fin m)

def glyzFrequencyBox {m : ℕ} (L : GlyzSpace m ≃L[ℝ] GlyzSpace m)
    (a : GlyzSpace m) (R : ℝ) : Set (GlyzSpace m) :=
  {ξ | ‖(EuclideanSpace.equiv (Fin m) ℝ) (L.symm (ξ - a))‖ ≤ R}

def glyzBoxCoordinates {m : ℕ} (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (x : GlyzSpace m) : Base m :=
  (EuclideanSpace.equiv (Fin m) ℝ) (glyzAdjointEquiv L x)

theorem glyzBoxCoordinates_apply {m : ℕ} (L : GlyzSpace m ≃L[ℝ] GlyzSpace m)
    (x : GlyzSpace m) (i : Fin m) :
    glyzBoxCoordinates L x i = inner ℝ x (L (EuclideanSpace.basisFun (Fin m) ℝ i)) := by
  rw [← glyzAdjointEquiv_inner L x, EuclideanSpace.inner_basisFun_real]
  rfl

def glyzPolarBox {m : ℕ} (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) : Set (GlyzSpace m) :=
  {x | ∀ i, |inner ℝ x (L (EuclideanSpace.basisFun (Fin m) ℝ i))| ≤ 1}

theorem glyzPolarBox_eq_preimage {m : ℕ} (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) :
    glyzPolarBox L = glyzAdjointEquiv L ⁻¹'
      ((EuclideanSpace.equiv (Fin m) ℝ) ⁻¹' closedBall 0 1) := by
  ext x
  simp only [glyzPolarBox, mem_setOf_eq, mem_preimage, mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg zero_le_one, Real.norm_eq_abs]
  simp_rw [← glyzBoxCoordinates_apply L x]
  rfl

theorem volume_glyzPolarBox {m : ℕ} (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) :
    volume (glyzPolarBox L) =
      ENNReal.ofReal |(LinearMap.det L.toLinearMap)⁻¹| * ENNReal.ofReal ((2 : ℝ) ^ m) := by
  let Q : Set (GlyzSpace m) := (EuclideanSpace.equiv (Fin m) ℝ) ⁻¹' closedBall 0 1
  have hQ : volume Q = ENNReal.ofReal ((2 : ℝ) ^ m) := by
    have hp : MeasurePreserving (EuclideanSpace.equiv (Fin m) ℝ) volume volume :=
      PiLp.volume_preserving_ofLp (Fin m)
    calc
      _ = Measure.map (EuclideanSpace.equiv (Fin m) ℝ) volume (closedBall (0 : Base m) 1) :=
        (Measure.map_apply (EuclideanSpace.equiv (Fin m) ℝ).continuous.measurable
          measurableSet_closedBall).symm
      _ = volume (closedBall (0 : Base m) 1) := congrArg (fun μ => μ (closedBall (0 : Base m) 1)) hp.map_eq
      _ = _ := by simp only [Real.volume_pi_closedBall (0 : Base m) (by norm_num : (0 : ℝ) ≤ 1),
        mul_one, Fintype.card_fin]
  rw [glyzPolarBox_eq_preimage]
  have ht := Measure.addHaar_preimage_linearMap (volume : Measure (GlyzSpace m))
    (f := (glyzAdjointEquiv L).toLinearMap)
    (LinearEquiv.isUnit_det' (glyzAdjointEquiv L).toLinearEquiv).ne_zero Q
  change volume (glyzAdjointEquiv L ⁻¹' Q) =
    ENNReal.ofReal |(LinearMap.det (glyzAdjointEquiv L).toLinearMap)⁻¹| * volume Q at ht
  rw [det_glyzAdjointEquiv, hQ] at ht
  exact ht

def glyzBoxWeight {m : ℕ} (A : ℕ) (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (x : GlyzSpace m) : ℝ :=
  |LinearMap.det L.toLinearMap| * glyzDecayWeight A (glyzBoxCoordinates L x)

def glyzPolarWeight {m : ℕ} (A : ℕ) (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (x : GlyzSpace m) : ℝ :=
  ((2 : ℝ) ^ m)⁻¹ * glyzBoxWeight A L x

theorem glyzPolarWeight_eq_volume {m : ℕ} (A : ℕ) (L : GlyzSpace m ≃L[ℝ] GlyzSpace m)
    (x : GlyzSpace m) :
    glyzPolarWeight A L x = (volume (glyzPolarBox L)).toReal⁻¹ *
      glyzDecayWeight A (glyzBoxCoordinates L x) := by
  rw [volume_glyzPolarBox, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (by positivity), mul_inv,
    abs_inv, inv_inv]
  unfold glyzPolarWeight glyzBoxWeight
  ring

theorem glyzAffineWeight_le_boxWeight {m : ℕ} (A : ℕ)
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (x : GlyzSpace m) :
    glyzAffineWeight A L x ≤ glyzBoxWeight A L x := by
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  unfold glyzNormWeight glyzDecayWeight
  apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
  apply pow_le_pow_left₀ (by positivity)
  apply max_le_max le_rfl
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le (glyzAdjointEquiv L x) i

theorem glyzFrequencyBox_subset_ball {m : ℕ} (L : GlyzSpace m ≃L[ℝ] GlyzSpace m)
    (a : GlyzSpace m) {R : ℝ} (hR : 0 < R) :
    glyzFrequencyBox L a R ⊆
      {ξ | ‖L.symm (ξ - a)‖ ≤ (‖(EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap‖ + 1) * R} := by
  intro ξ hξ
  calc
    _ = ‖(EuclideanSpace.equiv (Fin m) ℝ).symm
        ((EuclideanSpace.equiv (Fin m) ℝ) (L.symm (ξ - a)))‖ := by rw [ContinuousLinearEquiv.symm_apply_apply]
    _ ≤ ‖(EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap‖ *
        ‖(EuclideanSpace.equiv (Fin m) ℝ) (L.symm (ξ - a))‖ :=
      (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖(EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap‖ * R :=
      mul_le_mul_of_nonneg_left hξ (norm_nonneg _)
    _ ≤ _ := by nlinarith

/-- Uniform GLYZ uncertainty for actual affine Fourier boxes and their
volume-normalized polar-box weights. The constant precedes all frames,
centers, functions and physical points. -/
theorem glyz_uncertainty_fourier_box (m A : ℕ) (R : ℝ) (hR : 0 < R)
    {p : ℝ≥0} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (a : GlyzSpace m)
      (f : SchwartzMap (GlyzSpace m) ℂ),
      Function.support (𝓕 (f : GlyzSpace m → ℂ)) ⊆ glyzFrequencyBox L a R →
      ∀ x, ‖f x‖ₑ ^ (p : ℝ) ≤ ENNReal.ofReal C *
        ∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) * ENNReal.ofReal (glyzPolarWeight A L y) := by
  let S := (‖(EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap‖ + 1) * R
  have hS : 0 < S := mul_pos (by positivity) hR
  obtain ⟨C, hC, hunc⟩ := glyz_uncertainty_affine_ball (E := GlyzSpace m) A S hS hp
  refine ⟨C * 2 ^ m, mul_pos hC (by positivity), fun L a f hs x => ?_⟩
  have h := hunc L a f (hs.trans (glyzFrequencyBox_subset_ball L a hR)) x
  have hw (y : GlyzSpace m) : glyzBoxWeight A L y = 2 ^ m * glyzPolarWeight A L y := by
    unfold glyzPolarWeight
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ m ≠ 0), one_mul]
  calc
    _ ≤ ENNReal.ofReal C * ∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) *
        ENNReal.ofReal (glyzAffineWeight A L y) := h
    _ ≤ ENNReal.ofReal C * ∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) *
        ENNReal.ofReal (glyzBoxWeight A L y) := mul_le_mul_right
      (lintegral_mono (fun y => mul_le_mul_right (ENNReal.ofReal_le_ofReal
        (glyzAffineWeight_le_boxWeight A L y)) _)) _
    _ = _ := by
      simp_rw [hw, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ m)]
      rw [ENNReal.ofReal_mul hC.le]
      have he : (∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) *
          (ENNReal.ofReal (2 ^ m) * ENNReal.ofReal (glyzPolarWeight A L y))) =
          ENNReal.ofReal (2 ^ m) * ∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) *
            ENNReal.ofReal (glyzPolarWeight A L y) := by
        calc
          _ = ∫⁻ y, ENNReal.ofReal (2 ^ m) * (‖f (x - y)‖ₑ ^ (p : ℝ) *
              ENNReal.ofReal (glyzPolarWeight A L y)) := by
            apply lintegral_congr
            intro y
            ring
          _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      rw [he, mul_assoc]

end PlanarNikodym
