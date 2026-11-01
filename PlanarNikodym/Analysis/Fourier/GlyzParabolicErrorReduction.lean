import PlanarNikodym.Analysis.Fourier.GlyzRawChartParentStep

/-! The parabolic error depends on the original parent L¹ mass, with no
child-count loss and no loss from time normalization. -/
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem glyz_chart_error_factor_le (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (b : ℝ) (c : ℝ≥0) (p : ℝ) (err : ℝ≥0∞) :
    (ENNReal.ofReal b)⁻¹ *
      ((c : ℝ≥0∞) * ENNReal.ofReal |∏ i : Fin (k + 1), δ ^ (i : ℕ) / δ ^ k|)⁻¹ *
      ENNReal.ofReal δ ^ p * err ≤
      (ENNReal.ofReal b)⁻¹ * (c : ℝ≥0∞)⁻¹ * ENNReal.ofReal δ ^ p * err := by
  have hdet : (1 : ℝ≥0∞) ≤ ENNReal.ofReal |∏ i : Fin (k + 1), δ ^ (i : ℕ) / δ ^ k| := by
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (glyz_lowerDegreeDilation_abs_det_ge_one k hδ hδ1)
  have hh : (c : ℝ≥0∞) ≤ c * ENNReal.ofReal |∏ i : Fin (k + 1), δ ^ (i : ℕ) / δ ^ k| := by
    simpa only [mul_one] using mul_le_mul_right hdet (c : ℝ≥0∞)
  gcongr

theorem glyz_scaled_error_sum_le {ι : Type*} (I : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ I, 0 ≤ f i) {δ tail m p : ℝ}
    (hδ : 0 ≤ δ) (htail : 0 ≤ tail) (hp : 1 ≤ p)
    (hmass : δ * (∑ i ∈ I, f i) = m) :
    ENNReal.ofReal δ ^ p * (∑ i ∈ I, ENNReal.ofReal (tail * f i) ^ p) ≤
      ENNReal.ofReal tail ^ p * ENNReal.ofReal m ^ p := by
  have hs : (∑ i ∈ I, ENNReal.ofReal (tail * f i)) =
      ENNReal.ofReal (tail * (∑ i ∈ I, f i)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg htail (hf i hi)),
      Finset.mul_sum]
  have he : ENNReal.ofReal δ ^ p * (∑ i ∈ I, ENNReal.ofReal (tail * f i)) ^ p =
      ENNReal.ofReal tail ^ p * ENNReal.ofReal m ^ p := by
    rw [hs, ← ENNReal.mul_rpow_of_nonneg _ _ (zero_le_one.trans hp),
      ← ENNReal.ofReal_mul hδ]
    have hh : δ * (tail * (∑ i ∈ I, f i)) = tail * m := by rw [mul_left_comm, hmass]
    rw [hh, ENNReal.ofReal_mul htail, ENNReal.mul_rpow_of_nonneg _ _ (zero_le_one.trans hp)]
  exact (mul_le_mul_right (glyz_ennreal_sum_rpow_le_rpow_sum I
    (fun i => ENNReal.ofReal (tail * f i)) hp) _).trans_eq he

theorem glyz_scaled_error_sum_eq {ι : Type*} (I : Finset ι) (f : ι → ℝ)
    {δ tail m p : ℝ} (hδ : 0 ≤ δ) (htail : 0 ≤ tail) (hp : 0 ≤ p)
    (hmass : δ * (∑ i ∈ I, f i) = m) :
    ENNReal.ofReal δ ^ p * ENNReal.ofReal (∑ i ∈ I, tail * f i) ^ p =
      ENNReal.ofReal tail ^ p * ENNReal.ofReal m ^ p := by
  rw [← Finset.mul_sum, ← ENNReal.mul_rpow_of_nonneg _ _ hp, ← ENNReal.ofReal_mul hδ]
  have hh : δ * (tail * (∑ i ∈ I, f i)) = tail * m := by rw [mul_left_comm, hmass]
  rw [hh, ENNReal.ofReal_mul htail, ENNReal.mul_rpow_of_nonneg _ _ hp]

def glyzParabolicErrorCoefficient (k W M : ℕ) (p : ℝ≥0) (ε C D L δ α : ℝ)
    (N : ℕ) (T : ℝ) : ℝ≥0∞ :=
  let B : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (p : ℝ)
  let Q := ENNReal.ofReal (C * (2 : ℝ) ^
    (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N))
  let tail := D * (1 + |α|) ^ (volume : Measure (GlyzConeSpace k)).integrablePower * (T⁻¹) ^ M
  B * (Q * B * (∫⁻ x : GlyzConeSpace k, ENNReal.ofReal (glyzNormWeight W x)) +
    volume (closedBall (0 : GlyzConeSpace k) 1)) * ENNReal.ofReal tail ^ (p : ℝ) *
      ENNReal.ofReal (((δ ^ k)⁻¹ * L + 1) ^ Module.finrank ℝ (GlyzConeSpace k))

theorem glyz_scaled_parabolicPowerError_le (k W M : ℕ) (p : ℝ≥0) (hp : (1 : ℝ) ≤ p)
    (ε C D L δ α : ℝ) (hD : 0 ≤ D) (hδ : 0 < δ) (N : ℕ) (T : ℝ) (hT : 0 < T)
    (I : Finset ℕ) (g : ℕ → Plane → ℂ) (m : ℝ)
    (hmass : δ * (∑ i ∈ I, ∫ y, ‖g i y‖) = m) :
    ENNReal.ofReal δ ^ (p : ℝ) * glyzParabolicPowerError k W M p ε C D L δ α N T I g ≤
      glyzParabolicErrorCoefficient k W M p ε C D L δ α N T * ENNReal.ofReal m ^ (p : ℝ) := by
  let tail := D * (1 + |α|) ^ (volume : Measure (GlyzConeSpace k)).integrablePower * (T⁻¹) ^ M
  have htail : 0 ≤ tail := mul_nonneg (mul_nonneg hD (pow_nonneg (by positivity) _))
    (pow_nonneg (inv_nonneg.mpr hT.le) _)
  have hsum := glyz_scaled_error_sum_le I (fun i => ∫ y, ‖g i y‖)
    (fun i _ => integral_nonneg fun y => norm_nonneg _) hδ.le htail hp hmass
  have heq := glyz_scaled_error_sum_eq I (fun i => ∫ y, ‖g i y‖)
    hδ.le htail (zero_le_one.trans hp) hmass
  let B : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (p : ℝ)
  let Q := ENNReal.ofReal (C * (2 : ℝ) ^
    (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N))
  let w := ∫⁻ x : GlyzConeSpace k, ENNReal.ofReal (glyzNormWeight W x)
  let u := volume (closedBall (0 : GlyzConeSpace k) 1)
  let V := ENNReal.ofReal (((δ ^ k)⁻¹ * L + 1) ^ Module.finrank ℝ (GlyzConeSpace k))
  change ENNReal.ofReal δ ^ (p : ℝ) *
    (B * (Q * B * ((∑ i ∈ I, ENNReal.ofReal (tail * ∫ y, ‖g i y‖) ^ (p : ℝ)) * w) +
      ENNReal.ofReal (∑ i ∈ I, tail * ∫ y, ‖g i y‖) ^ (p : ℝ) * u) * V) ≤
      B * (Q * B * w + u) * ENNReal.ofReal tail ^ (p : ℝ) * V * ENNReal.ofReal m ^ (p : ℝ)
  calc
    _ = B * (Q * B * ((ENNReal.ofReal δ ^ (p : ℝ) *
        (∑ i ∈ I, ENNReal.ofReal (tail * ∫ y, ‖g i y‖) ^ (p : ℝ))) * w) +
        (ENNReal.ofReal δ ^ (p : ℝ) * ENNReal.ofReal
          (∑ i ∈ I, tail * ∫ y, ‖g i y‖) ^ (p : ℝ)) * u) * V := by ring
    _ ≤ B * (Q * B * ((ENNReal.ofReal tail ^ (p : ℝ) * ENNReal.ofReal m ^ (p : ℝ)) * w) +
        (ENNReal.ofReal tail ^ (p : ℝ) * ENNReal.ofReal m ^ (p : ℝ)) * u) * V := by
      rw [heq]
      gcongr
    _ = _ := by ring

/-- The geometric determinant can be discarded while the time Jacobian
still cancels the normalized L¹ mass exactly. -/
theorem glyz_chart_parabolic_error_le (k W M : ℕ) (p : ℝ≥0) (hp : (1 : ℝ) ≤ p)
    (ε C D L δ α : ℝ) (hD : 0 ≤ D) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (N : ℕ) (T : ℝ) (hT : 0 < T) (I : Finset ℕ) (g : ℕ → Plane → ℂ)
    (m b : ℝ) (c : ℝ≥0) (hmass : δ * (∑ i ∈ I, ∫ y, ‖g i y‖) = m) :
    (ENNReal.ofReal b)⁻¹ *
      ((c : ℝ≥0∞) * ENNReal.ofReal |∏ i : Fin (k + 1), δ ^ (i : ℕ) / δ ^ k|)⁻¹ *
      ENNReal.ofReal δ ^ (p : ℝ) * glyzParabolicPowerError k W M p ε C D L δ α N T I g ≤
      (ENNReal.ofReal b)⁻¹ * (c : ℝ≥0∞)⁻¹ *
        glyzParabolicErrorCoefficient k W M p ε C D L δ α N T * ENNReal.ofReal m ^ (p : ℝ) := by
  apply (glyz_chart_error_factor_le k hδ hδ1 b c p _).trans
  calc
    _ = (ENNReal.ofReal b)⁻¹ * (c : ℝ≥0∞)⁻¹ *
        (ENNReal.ofReal δ ^ (p : ℝ) * glyzParabolicPowerError k W M p ε C D L δ α N T I g) := by
      simp only [mul_assoc]
    _ ≤ (ENNReal.ofReal b)⁻¹ * (c : ℝ≥0∞)⁻¹ *
        (glyzParabolicErrorCoefficient k W M p ε C D L δ α N T * ENNReal.ofReal m ^ (p : ℝ)) :=
      mul_le_mul_right (glyz_scaled_parabolicPowerError_le k W M p hp ε C D L δ α hD hδ N T hT I g m hmass) _
    _ = _ := by simp only [mul_assoc]

theorem glyzParabolicPowerCoefficient_ne_top (k : ℕ) (p : ℝ≥0) (ε C Cg : ℝ) (N : ℕ) :
    glyzParabolicPowerCoefficient k p ε C Cg N ≠ ⊤ := by
  unfold glyzParabolicPowerCoefficient
  finiteness

theorem glyzParabolicErrorCoefficient_ne_top (k W M : ℕ)
    (hW : Module.finrank ℝ (GlyzConeSpace k) < W) (p : ℝ≥0)
    (ε C D L δ α : ℝ) (N : ℕ) (T : ℝ) :
    glyzParabolicErrorCoefficient k W M p ε C D L δ α N T ≠ ⊤ := by
  have hw := glyzNormWeight_lintegral_ne_top (E := GlyzConeSpace k) hW
  have hu : volume (closedBall (0 : GlyzConeSpace k) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  unfold glyzParabolicErrorCoefficient
  finiteness

end PlanarNikodym
