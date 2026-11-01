import PlanarNikodym.Analysis.Fourier.GlyzDyadicBlockSupport
import PlanarNikodym.Analysis.Fourier.GlyzProjectedFrequencyBox
import PlanarNikodym.Analysis.Fourier.GlyzEnlargedTaylorDecoupling

/-! Genuine nesting of the projected curve's Fourier boxes. The curve
is a linear image of the ambient moment curve: extend its coefficients
by zeros, use ambient moment nesting, and then project the parent box. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped FourierTransform BigOperators ENNReal NNReal
namespace PlanarNikodym

/-- Scalar dilation about a Fourier box's actual frequency center. -/
theorem glyzFrequencyBox_center_smul {m : ℕ}
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (a : GlyzSpace m)
    {R c : ℝ} {ξ : GlyzSpace m} (hξ : ξ ∈ glyzFrequencyBox L a R) :
    a + c • (ξ - a) ∈ glyzFrequencyBox L a (|c| * R) := by
  change ‖(EuclideanSpace.equiv (Fin m) ℝ) (L.symm ((a + c • (ξ - a)) - a))‖ ≤ _
  rw [add_sub_cancel_left, map_smul, map_smul, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hξ (abs_nonneg _)

/-- Every enlarged Fourier box is an actual dilation of its unit box. -/
theorem glyzFrequencyBox_eq_center_smul {m : ℕ}
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (a : GlyzSpace m) {R : ℝ} (hR : 0 < R) :
    glyzFrequencyBox L a R = (fun ξ => a + R • (ξ - a)) '' glyzFrequencyBox L a 1 := by
  ext ξ
  constructor
  · intro hξ
    refine ⟨a + R⁻¹ • (ξ - a), ?_, ?_⟩
    · have h := glyzFrequencyBox_center_smul L a (c := R⁻¹) hξ
      simpa [abs_of_pos hR, hR.ne'] using h
    · simp only [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
      abel
  · rintro ⟨η, hη, rfl⟩
    simpa only [abs_of_pos hR, mul_one] using glyzFrequencyBox_center_smul L a (c := R) hη

/-- Affine combinations remain in a box with the exact absolute
coefficient enlargement, including combinations with negative weights. -/
theorem glyzFrequencyBox_affine_combination {m : ℕ}
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (a : GlyzSpace m)
    {R c d : ℝ} (hcd : c + d = 1) {ξ η : GlyzSpace m}
    (hξ : ξ ∈ glyzFrequencyBox L a R) (hη : η ∈ glyzFrequencyBox L a R) :
    c • ξ + d • η ∈ glyzFrequencyBox L a ((|c| + |d|) * R) := by
  let Q := L.symm.trans (EuclideanSpace.equiv (Fin m) ℝ)
  change ‖Q (c • ξ + d • η - a)‖ ≤ _
  have he : c • ξ + d • η - a = c • (ξ - a) + d • (η - a) := by
    have ha : c • a + d • a = a := by rw [← add_smul, hcd, one_smul]
    calc
      _ = c • ξ + d • η - (c • a + d • a) := by rw [ha]
      _ = _ := by module
  rw [he, map_add, map_smul, map_smul]
  calc
    _ ≤ ‖c • Q (ξ - a)‖ + ‖d • Q (η - a)‖ := norm_add_le _ _
    _ = |c| * ‖Q (ξ - a)‖ + |d| * ‖Q (η - a)‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ |c| * R + |d| * R := add_le_add
      (mul_le_mul_of_nonneg_left hξ (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hη (abs_nonneg _))
    _ = _ := by ring

/-- Uniform ambient nesting for every fixed input radius. -/
theorem exists_uniform_glyzMomentFrequencyBox_enlarged_nested (m : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ (c κ s ρ : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ),
      s ∈ Icc (-1 : ℝ) 1 → ρ ≤ 1 →
      glyzFrequencyBox (glyzMomentFrequencyFrame m (c + κ * s) (κ * ρ) (mul_pos hκ hρ))
        ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m (c + κ * s))) R ⊆
      glyzFrequencyBox (glyzMomentFrequencyFrame m c κ hκ)
        ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m c)) Q := by
  obtain ⟨Q, hQ, hnest⟩ := exists_uniform_glyzMomentFrequencyBox_nested m
  refine ⟨(R + |1 - R|) * Q, by positivity, fun c κ s ρ hκ hρ hs hρ1 ξ hξ => ?_⟩
  rw [glyzFrequencyBox_eq_center_smul _ _ hR] at hξ
  obtain ⟨η, hη, rfl⟩ := hξ
  let a := (EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m (c + κ * s))
  have ha : a ∈ glyzMomentFrequencyBox m (c + κ * s) (κ * ρ) (mul_pos hκ hρ) := by
    change ‖(EuclideanSpace.equiv (Fin m) ℝ)
      ((glyzMomentFrequencyFrame m (c + κ * s) (κ * ρ) (mul_pos hκ hρ)).symm (a - a))‖ ≤ 1
    simp
  have h := glyzFrequencyBox_affine_combination
    (glyzMomentFrequencyFrame m c κ hκ)
    ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m c))
    (c := R) (d := 1 - R) (by ring) (hnest c κ s ρ hκ hρ hs hρ1 hη)
    (hnest c κ s ρ hκ hρ hs hρ1 ha)
  have he : a + R • (η - a) = R • η + (1 - R) • a := by module
  simpa only [abs_of_pos hR, ← he] using h

/-- A lower-dimensional curve box is the projection of ambient moment
coefficients after setting the higher-order coefficients to zero. -/
theorem glyzEnlargedCurveBox_subset_projected_moment (l r : ℕ)
    (t s δ R : ℝ) (hδ : 0 < δ) (hR : 0 ≤ R) :
    glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l s δ R ⊆
      glyzCoordinateProjection l r t ''
        glyzFrequencyBox (glyzMomentFrequencyFrame (l + r) s δ hδ)
          ((EuclideanSpace.equiv (Fin (l + r)) ℝ).symm (glyzMomentCurve (l + r) s)) R := by
  rintro ξ ⟨v, hv, rfl⟩
  let w : Base (l + r) := Fin.append v (fun _ => 0)
  let η := (EuclideanSpace.equiv (Fin (l + r)) ℝ).symm (glyzMomentCurve (l + r) s) +
    glyzMomentFrequencyFrame (l + r) s δ hδ ((EuclideanSpace.equiv (Fin (l + r)) ℝ).symm w)
  refine ⟨η, ?_, ?_⟩
  · rw [glyzFrequencyBox_eq_image]
    refine ⟨w, ?_, rfl⟩
    apply (mem_closedBall_zero_iff).mpr
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa [w, Real.norm_eq_abs] using hv j
    · simpa [w] using hR
  · dsimp only [η]
    rw [glyzMomentFrequencyFrame_coordinates, map_add, map_sum]
    simp_rw [map_smul, glyzCoordinateProjection_jet]
    rw [Fin.sum_univ_add]
    simp only [w, Fin.append_left, Fin.append_right, Fin.val_castAdd,
      mul_zero, zero_smul, Finset.sum_const_zero, add_zero]
    rfl

/-- Projecting an arbitrary fixed enlarged ambient box gives a uniformly
enlarged box of the actual controlled curve. -/
theorem exists_uniform_glyz_projected_enlarged_frequencyBox
    (l r : ℕ) {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ z ∈ separatedMixedCenters ν,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
        glyzCoordinateProjection l r z.2 ''
          glyzFrequencyBox (glyzMomentFrequencyFrame (l + r) z.1 δ hδ)
            ((EuclideanSpace.equiv (Fin (l + r)) ℝ).symm (glyzMomentCurve (l + r) z.1)) R ⊆
          glyzEnlargedCurveBox (glyzCoordinateCurve l r z.2) l z.1 δ Q := by
  obtain ⟨Q, hQ, hproj⟩ := exists_uniform_glyz_projected_frequencyBox l r hν
  refine ⟨R * Q, mul_pos hR hQ, fun z hz δ hδ hδ1 ξ hξ => ?_⟩
  obtain ⟨L, hL, hproj⟩ := hproj z hz
  rw [glyzEnlargedCurveBox_eq_frequencyBox _ _ _ _ hδ (mul_pos hR hQ).le L hL]
  obtain ⟨η, hη, rfl⟩ := hξ
  rw [glyzFrequencyBox_eq_center_smul _ _ hR] at hη
  obtain ⟨ζ, hζ, rfl⟩ := hη
  have hp := hproj δ hδ hδ1 ⟨ζ, hζ, rfl⟩
  have hc : glyzCoordinateProjection l r z.2
      ((EuclideanSpace.equiv (Fin (l + r)) ℝ).symm (glyzMomentCurve (l + r) z.1)) =
      glyzCoordinateCurve l r z.2 z.1 := rfl
  rw [map_add, map_smul, map_sub, hc]
  simpa only [abs_of_pos hR] using
    glyzFrequencyBox_center_smul (glyzScaledFrame L δ hδ)
      (glyzCoordinateCurve l r z.2 z.1) (c := R) hp

/-- Every fine projected-curve box in a parent parameter interval lies
in a uniformly enlarged parent curve box. No support hypothesis about
coarse block sums is assumed. -/
theorem exists_uniform_glyzEnlargedCurveBox_nested
    (l r : ℕ) {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ (t c κ s ρ : ℝ), 0 < κ → 0 < ρ →
      (c, t) ∈ separatedMixedCenters ν → κ ≤ 1 →
      s ∈ Icc (-1 : ℝ) 1 → ρ ≤ 1 →
      glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l (c + κ * s) (κ * ρ) R ⊆
        glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l c κ Q := by
  obtain ⟨B, hB, hnest⟩ := exists_uniform_glyzMomentFrequencyBox_enlarged_nested (l + r) hR
  obtain ⟨Q, hQ, hproj⟩ := exists_uniform_glyz_projected_enlarged_frequencyBox l r hν hB
  refine ⟨Q, hQ, fun t c κ s ρ hκ hρ hsep hκ1 hs hρ1 => ?_⟩
  exact (glyzEnlargedCurveBox_subset_projected_moment l r t (c + κ * s) (κ * ρ) R
    (mul_pos hκ hρ) hR.le).trans
      ((Set.image_mono (hnest c κ s ρ hκ hρ hs hρ1)).trans (hproj (c, t) hsep κ hκ hκ1))

/-- Every dyadic descendant curve box lies in the same uniformly
enlarged parent curve box. -/
theorem exists_uniform_glyz_dyadic_curve_descendant_box
    (l r : ℕ) {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ (t : ℝ) (n q i j : ℕ), j < 2 ^ q →
      (glyzDyadicCenter n i, t) ∈ separatedMixedCenters ν →
      glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
        (glyzDyadicCenter (n + q) (i * 2 ^ q + j)) (glyzDyadicScale (n + q)) R ⊆
        glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
          (glyzDyadicCenter n i) (glyzDyadicScale n) Q := by
  obtain ⟨Q, hQ, hnest⟩ := exists_uniform_glyzEnlargedCurveBox_nested l r hν hR
  refine ⟨Q, hQ, fun t n q i j hj hsep => ?_⟩
  have hc : glyzDyadicCenter n i + glyzDyadicScale n * (glyzDyadicCenter q j - 1 / 2) =
      glyzDyadicCenter (n + q) (i * 2 ^ q + j) := by
    rw [← glyzDyadicCenter_rescale]
    unfold glyzDyadicCenter
    ring
  have hjc := glyzDyadicCenter_mem_Icc hj
  have hs : glyzDyadicCenter q j - 1 / 2 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hjc.1, hjc.2]
  have hscale (k : ℕ) : glyzDyadicScale k ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have h := hnest t (glyzDyadicCenter n i) (glyzDyadicScale n)
    (glyzDyadicCenter q j - 1 / 2) (glyzDyadicScale q)
    (glyzDyadicScale_pos n) (glyzDyadicScale_pos q) hsep (hscale n) hs (hscale q)
  rw [hc, ← glyzDyadicScale_add] at h
  exact h

/-- Actual fine Fourier support alone gives the support of every
coarse dyadic sum in a uniformly enlarged projected-curve parent box.
This discharges the support hypotheses of the finite-scale iteration. -/
theorem exists_uniform_glyz_dyadic_curve_block_support
    (l r : ℕ) {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ (t : ℝ) (N n i : ℕ), n ≤ N → i < 2 ^ n →
      (glyzDyadicCenter n i, t) ∈ separatedMixedCenters ν →
      ∀ f : ℕ → SchwartzMap (GlyzSpace l) ℂ,
      (∀ j < 2 ^ N, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
          (glyzDyadicCenter N j) (glyzDyadicScale N) R) →
      Function.support (𝓕 ((glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace l) ℂ) :
        GlyzSpace l → ℂ)) ⊆ glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
          (glyzDyadicCenter n i) (glyzDyadicScale n) Q := by
  classical
  obtain ⟨Q, hQ, hnest⟩ := exists_uniform_glyz_dyadic_curve_descendant_box l r hν hR
  refine ⟨Q, hQ, fun t N n i hn hi hsep f hf ξ hξ => ?_⟩
  by_contra hout
  have he : n + (N - n) = N := Nat.add_sub_of_le hn
  have hz (j : ℕ) (hj : j < 2 ^ (N - n)) :
      𝓕 (f (i * 2 ^ (N - n) + j) : GlyzSpace l → ℂ) ξ = 0 := by
    by_contra hjz
    apply hout
    apply hnest t n (N - n) i j hj hsep
    have hidx : i * 2 ^ (N - n) + j < 2 ^ N := by
      simpa only [he] using glyz_dyadic_descendant_lt hi hj
    simpa only [he] using hf _ hidx hjz
  apply hξ
  change (𝓕 (∑ j ∈ Finset.range (2 ^ (N - n)), f (i * 2 ^ (N - n) + j) :
    SchwartzMap (GlyzSpace l) ℂ)) ξ = 0
  simp only [FourierTransform.fourier_sum, sum_apply]
  exact Finset.sum_eq_zero fun j hj => hz j (Finset.mem_range.mp hj)

end PlanarNikodym
