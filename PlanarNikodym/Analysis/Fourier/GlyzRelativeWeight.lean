import PlanarNikodym.Analysis.Fourier.GlyzPolarBilinearMeasure

/-! A two-region estimate for actual polar weights in different frames.
The density loss and the coordinate contraction are kept explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace PlanarNikodym

theorem glyzRelativeWeight_two_region {m A : ℕ}
    (Q₁ Q₂ : GlyzSpace m →ₗ[ℝ] Base m) {d₁ d₂ δ K : ℝ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hδ : 0 ≤ δ) (hK : 1 ≤ K)
    (hpow : δ ^ A * d₁ ≤ K * d₂)
    (hQ : ∀ z, ‖Q₂ z‖ ≤ δ * ‖Q₁ z‖) (x y : GlyzSpace m) :
    (d₁ * glyzDecayWeight A (Q₁ (x - y))) * (d₂ * glyzDecayWeight A (Q₂ y)) ≤
      2 ^ A * K * (d₂ * glyzDecayWeight A (Q₂ x)) *
        (d₁ * glyzDecayWeight A (Q₁ (x - y)) + d₂ * glyzDecayWeight A (Q₂ y)) := by
  let u := max (1 : ℝ) ‖Q₂ x‖
  let v := max (1 : ℝ) ‖Q₂ y‖
  let z := max (1 : ℝ) ‖Q₁ (x - y)‖
  have hu : 0 < u := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hv : 0 < v := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hz : 0 < z := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hK0 : 0 ≤ K := by linarith
  have hwx := (glyzDecayWeight_pos A (Q₂ x)).le
  have hwy := (glyzDecayWeight_pos A (Q₂ y)).le
  have hwz := (glyzDecayWeight_pos A (Q₁ (x - y))).le
  by_cases h : u ≤ 2 * v
  · have hp := pow_le_pow_left₀ hu.le h A
    rw [mul_pow] at hp
    have hh : glyzDecayWeight A (Q₂ y) ≤ 2 ^ A * glyzDecayWeight A (Q₂ x) := by
      change (v ^ A)⁻¹ ≤ 2 ^ A * (u ^ A)⁻¹
      have hh : (1 : ℝ) / v ^ A ≤ 2 ^ A / u ^ A :=
        (div_le_div_iff₀ (pow_pos hv A) (pow_pos hu A)).mpr (by simpa using hp)
      simpa only [one_div, div_eq_mul_inv, one_mul] using hh
    calc
      _ ≤ (d₁ * glyzDecayWeight A (Q₁ (x - y))) *
          (d₂ * (2 ^ A * glyzDecayWeight A (Q₂ x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hd₂.le) (by positivity)
      _ = (2 ^ A * (d₂ * glyzDecayWeight A (Q₂ x))) *
          (d₁ * glyzDecayWeight A (Q₁ (x - y))) := by ring
      _ ≤ (2 ^ A * K * (d₂ * glyzDecayWeight A (Q₂ x))) *
          (d₁ * glyzDecayWeight A (Q₁ (x - y))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [show 0 ≤ 2 ^ A * (d₂ * glyzDecayWeight A (Q₂ x)) by positivity]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg hd₂.le hwy)) (by positivity)
  · have hlarge : 1 < u := by
      have : 1 ≤ v := le_max_left _ _
      linarith
    have he : u = ‖Q₂ x‖ := max_eq_right
      (((lt_max_iff.mp hlarge).resolve_left (lt_irrefl _)).le)
    have htri : u ≤ δ * ‖Q₁ (x - y)‖ + v := by
      rw [he]
      calc
        ‖Q₂ x‖ = ‖Q₂ (x - y) + Q₂ y‖ := by rw [map_sub, sub_add_cancel]
        _ ≤ ‖Q₂ (x - y)‖ + ‖Q₂ y‖ := norm_add_le _ _
        _ ≤ δ * ‖Q₁ (x - y)‖ + v := add_le_add (hQ _) (le_max_right _ _)
    have hnorm : u ≤ 2 * δ * z := by
      have hz' : ‖Q₁ (x - y)‖ ≤ z := le_max_right _ _
      have := mul_le_mul_of_nonneg_left hz' hδ
      linarith
    have hp := pow_le_pow_left₀ hu.le hnorm A
    simp only [mul_pow] at hp
    have hp' : d₁ * u ^ A ≤ 2 ^ A * K * d₂ * z ^ A := by
      calc
        _ ≤ d₁ * (2 ^ A * δ ^ A * z ^ A) := mul_le_mul_of_nonneg_left hp hd₁.le
        _ = (2 ^ A * z ^ A) * (δ ^ A * d₁) := by ring
        _ ≤ (2 ^ A * z ^ A) * (K * d₂) := mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = _ := by ring
    have hh : d₁ * glyzDecayWeight A (Q₁ (x - y)) ≤
        2 ^ A * K * (d₂ * glyzDecayWeight A (Q₂ x)) := by
      change d₁ * (z ^ A)⁻¹ ≤ 2 ^ A * K * (d₂ * (u ^ A)⁻¹)
      have hh : d₁ / z ^ A ≤ (2 ^ A * K * d₂) / u ^ A :=
        (div_le_div_iff₀ (pow_pos hz A) (pow_pos hu A)).mpr hp'
      simpa only [div_eq_mul_inv, mul_assoc] using hh
    calc
      _ ≤ (2 ^ A * K * (d₂ * glyzDecayWeight A (Q₂ x))) *
          (d₂ * glyzDecayWeight A (Q₂ y)) :=
        mul_le_mul_of_nonneg_right hh (mul_nonneg hd₂.le hwy)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (mul_nonneg hd₁.le hwz)) (by positivity)

/-- Actual frame weights, including their polar-volume normalizations. -/
theorem glyzPolarWeight_two_region {m A : ℕ}
    (L₁ L₂ : GlyzSpace m ≃L[ℝ] GlyzSpace m) {δ K : ℝ}
    (hδ : 0 ≤ δ) (hK : 1 ≤ K)
    (hpow : δ ^ A * |LinearMap.det L₁.toLinearMap| ≤ K * |LinearMap.det L₂.toLinearMap|)
    (hQ : ∀ z, ‖glyzBoxCoordinates L₂ z‖ ≤ δ * ‖glyzBoxCoordinates L₁ z‖)
    (x y : GlyzSpace m) :
    glyzPolarWeight A L₁ (x - y) * glyzPolarWeight A L₂ y ≤
      2 ^ A * K * glyzPolarWeight A L₂ x *
        (glyzPolarWeight A L₁ (x - y) + glyzPolarWeight A L₂ y) := by
  let Q (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) :=
    (EuclideanSpace.equiv (Fin m) ℝ).toLinearMap.comp (glyzAdjointEquiv L).toLinearMap
  have hd (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) :
      0 < ((2 : ℝ) ^ m)⁻¹ * |LinearMap.det L.toLinearMap| :=
    mul_pos (by positivity) (abs_pos.mpr (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero)
  have hp : δ ^ A * (((2 : ℝ) ^ m)⁻¹ * |LinearMap.det L₁.toLinearMap|) ≤
      K * (((2 : ℝ) ^ m)⁻¹ * |LinearMap.det L₂.toLinearMap|) := by
    nlinarith [mul_le_mul_of_nonneg_left hpow (show 0 ≤ ((2 : ℝ) ^ m)⁻¹ by positivity)]
  have h := glyzRelativeWeight_two_region (Q L₁) (Q L₂) (hd L₁) (hd L₂) hδ hK hp hQ x y
  have he (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (z : GlyzSpace m) :
      Q L z = glyzBoxCoordinates L z := rfl
  simp_rw [he] at h
  unfold glyzPolarWeight glyzBoxWeight
  nlinarith only [h]

/-- Lebesgue convolution bound, with a completely explicit finite constant. -/
theorem integral_glyzPolarWeight_convolution_le {m A : ℕ} (hA : m < A)
    (L₁ L₂ : GlyzSpace m ≃L[ℝ] GlyzSpace m) {δ K : ℝ}
    (hδ : 0 ≤ δ) (hK : 1 ≤ K)
    (hpow : δ ^ A * |LinearMap.det L₁.toLinearMap| ≤ K * |LinearMap.det L₂.toLinearMap|)
    (hQ : ∀ z, ‖glyzBoxCoordinates L₂ z‖ ≤ δ * ‖glyzBoxCoordinates L₁ z‖)
    (x : GlyzSpace m) :
    (∫ y, glyzPolarWeight A L₁ (x - y) * glyzPolarWeight A L₂ y) ≤
      (2 ^ (A + 1) * K * (((2 : ℝ) ^ m)⁻¹ * ∫ y : Base m, glyzDecayWeight A y)) *
        glyzPolarWeight A L₂ x := by
  have hf := (integrable_glyzPolarWeight hA L₁).comp_sub_left x
  have hg := integrable_glyzPolarWeight hA L₂
  have hprod : Integrable (fun y => glyzPolarWeight A L₁ (x - y) * glyzPolarWeight A L₂ y) := by
    apply (hg.const_mul (((2 : ℝ) ^ m)⁻¹ * |LinearMap.det L₁.toLinearMap|)).mono'
      (((continuous_glyzPolarWeight A L₁).comp (continuous_const.sub continuous_id)).mul
        (continuous_glyzPolarWeight A L₂)).aestronglyMeasurable
    filter_upwards [] with y
    change |glyzPolarWeight A L₁ (x - y) * glyzPolarWeight A L₂ y| ≤ _
    rw [abs_of_pos (mul_pos (glyzPolarWeight_pos A L₁ _) (glyzPolarWeight_pos A L₂ _))]
    apply mul_le_mul_of_nonneg_right _ (glyzPolarWeight_pos A L₂ y).le
    unfold glyzPolarWeight glyzBoxWeight
    nlinarith [glyzDecayWeight_le_one A (glyzBoxCoordinates L₁ (x - y)),
      show 0 ≤ ((2 : ℝ) ^ m)⁻¹ * |LinearMap.det L₁.toLinearMap| by positivity]
  calc
    _ ≤ ∫ y, 2 ^ A * K * glyzPolarWeight A L₂ x *
        (glyzPolarWeight A L₁ (x - y) + glyzPolarWeight A L₂ y) :=
      integral_mono hprod ((hf.add hg).const_mul _) (glyzPolarWeight_two_region L₁ L₂ hδ hK hpow hQ x)
    _ = _ := by
      rw [integral_const_mul, integral_add hf hg, integral_sub_left_eq_self,
        integral_glyzPolarWeight, integral_glyzPolarWeight, pow_succ]
      ring

end PlanarNikodym
