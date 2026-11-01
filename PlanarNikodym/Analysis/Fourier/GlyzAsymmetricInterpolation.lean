import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricConstants

/-! Hölder interpolation for the actual optimal asymmetric constants.
Both the frequency support and the separated-parent quantifiers are
retained when passing from integral inequalities to optimal constants. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace PlanarNikodym

theorem glyz_mixed_energy_logaffine {F G p a₀ a₁ θ : ℝ}
    (hF : 0 ≤ F) (hG : 0 ≤ G) (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (hap₀ : a₀ ≤ p) (hap₁ : a₁ ≤ p) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (F ^ (a₁ / 2) * G ^ ((p - a₁) / 2)) ^ θ *
      (F ^ (a₀ / 2) * G ^ ((p - a₀) / 2)) ^ (1 - θ) =
      F ^ ((θ * a₁ + (1 - θ) * a₀) / 2) *
        G ^ ((p - (θ * a₁ + (1 - θ) * a₀)) / 2) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hF _) (Real.rpow_nonneg hG _),
    Real.mul_rpow (Real.rpow_nonneg hF _) (Real.rpow_nonneg hG _),
    ← Real.rpow_mul hF, ← Real.rpow_mul hG, ← Real.rpow_mul hF, ← Real.rpow_mul hG]
  have hF' : F ^ (a₁ / 2 * θ) * F ^ (a₀ / 2 * (1 - θ)) =
      F ^ ((θ * a₁ + (1 - θ) * a₀) / 2) := by
    rw [← Real.rpow_add_of_nonneg hF (by positivity) (by positivity)]
    congr 1
    ring
  have hG' : G ^ ((p - a₁) / 2 * θ) * G ^ ((p - a₀) / 2 * (1 - θ)) =
      G ^ ((p - (θ * a₁ + (1 - θ) * a₀)) / 2) := by
    rw [← Real.rpow_add_of_nonneg hG (by positivity) (by positivity)]
    congr 1
    ring
  calc
    _ = (F ^ (a₁ / 2 * θ) * F ^ (a₀ / 2 * (1 - θ))) *
        (G ^ ((p - a₁) / 2 * θ) * G ^ ((p - a₀) / 2 * (1 - θ))) := by ring
    _ = _ := by rw [hF', hG']

theorem glyzDyadicBilinearEnergy_logaffine (m N n n' : ℕ) (p : ℝ≥0)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (i j : ℕ) {a₀ a₁ θ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hap₀ : a₀ ≤ (p : ℝ))
    (hap₁ : a₁ ≤ (p : ℝ)) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    glyzDyadicBilinearEnergy m N n n' p a₁ f i j ^ θ *
      glyzDyadicBilinearEnergy m N n n' p a₀ f i j ^ (1 - θ) =
      glyzDyadicBilinearEnergy m N n n' p (θ * a₁ + (1 - θ) * a₀) f i j :=
  glyz_mixed_energy_logaffine
    (glyz_dyadic_square_block_nonneg m N n i p f)
    (glyz_dyadic_square_block_nonneg m N n' j p f) ha₀ ha₁ hap₀ hap₁ hθ hθ1

theorem glyzDyadicBilinearValue_logconvex {m A : ℕ} (hA : m < A)
    (N n n' : ℕ) (p : ℝ≥0) (hp : 0 < p)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (i j : ℕ) {a₀ a₁ θ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hap₀ : a₀ ≤ (p : ℝ))
    (hap₁ : a₁ ≤ (p : ℝ)) (hθ : 0 < θ) (hθ1 : θ < 1) :
    glyzDyadicBilinearValue m A N n n' p (θ * a₁ + (1 - θ) * a₀) f i j ≤
      glyzDyadicBilinearValue m A N n n' p a₁ f i j ^ θ *
        glyzDyadicBilinearValue m A N n n' p a₀ f i j ^ (1 - θ) := by
  let μ := glyzDyadicPolarMeasure m A n i
  let ν := glyzDyadicPolarMeasure m A n' j
  letI : IsFiniteMeasure μ := isFiniteMeasure_glyzPolarMeasure hA _
  letI : IsFiniteMeasure ν := isFiniteMeasure_glyzPolarMeasure hA _
  have h := glyzWeightedBilinear_logconvex μ ν
    (glyzDyadicBlock f N n i) (glyzDyadicBlock f N n' j)
    ha₀ ha₁ (sub_nonneg.mpr hap₀) (sub_nonneg.mpr hap₁) hθ hθ1
  have he : θ * ((p : ℝ) - a₁) + (1 - θ) * ((p : ℝ) - a₀) =
      (p : ℝ) - (θ * a₁ + (1 - θ) * a₀) := by ring
  rw [he] at h
  have hfinite₁ := glyzWeightedBilinear_lt_top μ ν
    (glyzDyadicBlock f N n i) (glyzDyadicBlock f N n' j) (show (0 : ℝ) < p from hp) ha₁ hap₁
  have hfinite₀ := glyzWeightedBilinear_lt_top μ ν
    (glyzDyadicBlock f N n i) (glyzDyadicBlock f N n' j) (show (0 : ℝ) < p from hp) ha₀ hap₀
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hθ.le hfinite₁.ne)
    (ENNReal.rpow_ne_top_of_nonneg (sub_pos.mpr hθ1).le hfinite₀.ne)) h
  simpa only [glyzDyadicBilinearValue, μ, ν, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow] using ht

theorem glyz_asymmetric_integral_bound_logconvex {m A N n n' : ℕ} (hA : m < A)
    {p : ℝ≥0} (hp : 0 < p) {a₀ a₁ θ C₀ C₁ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hap₀ : a₀ ≤ (p : ℝ))
    (hap₁ : a₁ ≤ (p : ℝ)) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hC₀ : GlyzAsymmetricIntegralBound m A N n n' p a₀ C₀)
    (hC₁ : GlyzAsymmetricIntegralBound m A N n n' p a₁ C₁) :
    GlyzAsymmetricIntegralBound m A N n n' p (θ * a₁ + (1 - θ) * a₀)
      (C₁ ^ θ * C₀ ^ (1 - θ)) := by
  refine ⟨mul_nonneg (Real.rpow_nonneg hC₁.1 _) (Real.rpow_nonneg hC₀.1 _),
    fun f hf i hi j hj hs => ?_⟩
  have h := glyzDyadicBilinearValue_logconvex hA N n n' p hp f i j
    ha₀ ha₁ hap₀ hap₁ hθ hθ1
  have h₁ := Real.rpow_le_rpow ENNReal.toReal_nonneg
    (hC₁.2 f hf i hi j hj hs) hθ.le
  have h₀ := Real.rpow_le_rpow ENNReal.toReal_nonneg
    (hC₀.2 f hf i hi j hj hs) (sub_pos.mpr hθ1).le
  apply (h.trans (mul_le_mul h₁ h₀
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (Real.rpow_nonneg (mul_nonneg hC₁.1
      (glyzDyadicBilinearEnergy_nonneg m N n n' p a₁ f i j)) _))).trans_eq
  rw [Real.mul_rpow hC₁.1 (glyzDyadicBilinearEnergy_nonneg m N n n' p a₁ f i j),
    Real.mul_rpow hC₀.1 (glyzDyadicBilinearEnergy_nonneg m N n n' p a₀ f i j)]
  calc
    _ = (C₁ ^ θ * C₀ ^ (1 - θ)) *
        (glyzDyadicBilinearEnergy m N n n' p a₁ f i j ^ θ *
          glyzDyadicBilinearEnergy m N n n' p a₀ f i j ^ (1 - θ)) := by ring
    _ = _ := by rw [glyzDyadicBilinearEnergy_logaffine m N n n' p f i j
      ha₀ ha₁ hap₀ hap₁ hθ.le hθ1.le]

theorem glyzAsymmetricIntegralConstant_logconvex {m A : ℕ} (hA : m < A)
    (N n n' : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) {a₀ a₁ θ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hap₀ : a₀ ≤ (p : ℝ))
    (hap₁ : a₁ ≤ (p : ℝ)) (hθ : 0 < θ) (hθ1 : θ < 1) :
    glyzAsymmetricIntegralConstant m A N n n' p (θ * a₁ + (1 - θ) * a₀) ≤
      glyzAsymmetricIntegralConstant m A N n n' p a₁ ^ θ *
        glyzAsymmetricIntegralConstant m A N n n' p a₀ ^ (1 - θ) :=
  glyzAsymmetricIntegralConstant_le (glyz_asymmetric_integral_bound_logconvex hA
    (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hp) ha₀ ha₁ hap₀ hap₁ hθ hθ1
    (glyzAsymmetricIntegralConstant_bound hA N n n' p hp ha₀ hap₀)
    (glyzAsymmetricIntegralConstant_bound hA N n n' p hp ha₁ hap₁))

theorem glyz_admissible_asymmetric_loss_logconvex {m A : ℕ} (hA : m < A)
    (p : ℝ≥0) (hp : 1 ≤ p) {a₀ a₁ θ alpha beta e₀ e₁ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hap₀ : a₀ ≤ (p : ℝ))
    (hap₁ : a₁ ≤ (p : ℝ)) (hθ : 0 < θ) (hθ1 : θ < 1)
    (he₀ : GlyzAdmissibleAsymmetricLoss m A p a₀ alpha beta e₀)
    (he₁ : GlyzAdmissibleAsymmetricLoss m A p a₁ alpha beta e₁) :
    GlyzAdmissibleAsymmetricLoss m A p (θ * a₁ + (1 - θ) * a₀) alpha beta
      (θ * e₁ + (1 - θ) * e₀) := by
  obtain ⟨he₀, C₀, hC₀, h₀⟩ := he₀
  obtain ⟨he₁, C₁, hC₁, h₁⟩ := he₁
  have hθ' : 0 < 1 - θ := sub_pos.mpr hθ1
  refine ⟨add_nonneg (mul_nonneg hθ.le he₁) (mul_nonneg hθ'.le he₀),
    C₁ ^ θ * C₀ ^ (1 - θ),
    mul_pos (Real.rpow_pos_of_pos hC₁ _) (Real.rpow_pos_of_pos hC₀ _), fun N => ?_⟩
  have hB₁ := Real.rpow_le_rpow
    (glyzAsymmetricIntegralConstant_nonneg hA N _ _ p hp ha₁ hap₁) (h₁ N) hθ.le
  have hB₀ := Real.rpow_le_rpow
    (glyzAsymmetricIntegralConstant_nonneg hA N _ _ p hp ha₀ hap₀) (h₀ N) hθ'.le
  apply (glyzAsymmetricIntegralConstant_logconvex hA N _ _ p hp
    ha₀ ha₁ hap₀ hap₁ hθ hθ1).trans
  apply (mul_le_mul hB₁ hB₀
    (Real.rpow_nonneg (glyzAsymmetricIntegralConstant_nonneg hA N _ _ p hp ha₀ hap₀) _)
    (Real.rpow_nonneg (mul_nonneg hC₁.le (Real.rpow_nonneg (by norm_num) _)) _)).trans_eq
  rw [Real.mul_rpow hC₁.le (Real.rpow_nonneg (by norm_num) _),
    Real.mul_rpow hC₀.le (Real.rpow_nonneg (by norm_num) _)]
  have hpow : ((2 : ℝ) ^ (e₁ * N)) ^ θ * ((2 : ℝ) ^ (e₀ * N)) ^ (1 - θ) =
      (2 : ℝ) ^ ((θ * e₁ + (1 - θ) * e₀) * N) := by
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  calc
    _ = (C₁ ^ θ * C₀ ^ (1 - θ)) *
        (((2 : ℝ) ^ (e₁ * N)) ^ θ * ((2 : ℝ) ^ (e₀ * N)) ^ (1 - θ)) := by ring
    _ = _ := by rw [hpow]

/-- Hölder also survives optimization over all uniform growth
exponents. The argument approximates both infima from above, so it
does not assume either infimum is attained. -/
theorem glyzOptimalAsymmetricLoss_logconvex {m A : ℕ} (hA : m < A)
    (p : ℝ≥0) (hp : 1 ≤ p) {a₀ a₁ θ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hap₀ : a₀ ≤ (p : ℝ))
    (hap₁ : a₁ ≤ (p : ℝ)) (hθ : 0 < θ) (hθ1 : θ < 1) (alpha beta : ℝ) :
    glyzOptimalAsymmetricLoss m A p (θ * a₁ + (1 - θ) * a₀) alpha beta ≤
      θ * glyzOptimalAsymmetricLoss m A p a₁ alpha beta +
        (1 - θ) * glyzOptimalAsymmetricLoss m A p a₀ alpha beta := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have h₀ := glyz_admissible_asymmetric_loss_of_optimal_lt hA p hp ha₀ hap₀ alpha beta
    (show glyzOptimalAsymmetricLoss m A p a₀ alpha beta <
      glyzOptimalAsymmetricLoss m A p a₀ alpha beta + ε by linarith)
  have h₁ := glyz_admissible_asymmetric_loss_of_optimal_lt hA p hp ha₁ hap₁ alpha beta
    (show glyzOptimalAsymmetricLoss m A p a₁ alpha beta <
      glyzOptimalAsymmetricLoss m A p a₁ alpha beta + ε by linarith)
  have h := glyzOptimalAsymmetricLoss_le
    (glyz_admissible_asymmetric_loss_logconvex hA p hp ha₀ ha₁ hap₀ hap₁ hθ hθ1 h₀ h₁)
  calc
    _ ≤ θ * (glyzOptimalAsymmetricLoss m A p a₁ alpha beta + ε) +
        (1 - θ) * (glyzOptimalAsymmetricLoss m A p a₀ alpha beta + ε) := h
    _ = _ := by ring

end PlanarNikodym
