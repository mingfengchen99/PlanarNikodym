import PlanarNikodym.Analysis.Fourier.GlyzAffineCutoff
import PlanarNikodym.Analysis.Fourier.GlyzSchwartzRescaling
import PlanarNikodym.Analysis.Fourier.GlyzLocalAverage
import PlanarNikodym.Analysis.Fourier.GlyzScaledCurveFrame

/-! Support-preserving spatial localization for GLYZ Corollary 3.7.
The cutoff is constructed from a compactly supported Fourier bump. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory FourierTransform
open scoped FourierTransform Convolution ENNReal NNReal Pointwise
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual Fourier transform of a Schwartz product is the convolution
of its Fourier transforms. -/
theorem glyz_fourier_schwartz_product (f g : SchwartzMap E ℂ) :
    𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g) =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap E ℂ)).symm.injective
  rw [FourierTransform.fourierEquiv_symm_apply, FourierTransform.fourierEquiv_symm_apply,
    fourierInv_fourier_eq]
  ext x
  change f x * g x = (𝓕⁻ (_ : SchwartzMap E ℂ)) x
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg,
    ← SchwartzMap.fourier_coe, SchwartzMap.fourier_convolution]
  change f x * g x = 𝓕 (𝓕 f) (-x) * 𝓕 (𝓕 g) (-x)
  have hf : 𝓕 (𝓕 f) (-x) = f x := by
    rw [SchwartzMap.fourier_coe, ← Real.fourierInv_eq_fourier_neg,
      ← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq]
  have hg : 𝓕 (𝓕 g) (-x) = g x := by
    rw [SchwartzMap.fourier_coe, ← Real.fourierInv_eq_fourier_neg,
      ← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq]
  rw [hf, hg]

/-- Multiplication by a bandlimited spatial cutoff enlarges Fourier
support by precisely a Minkowski sum. -/
theorem support_fourier_glyz_schwartz_product (f g : SchwartzMap E ℂ) :
    Function.support (𝓕 ((SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g) : E → ℂ)) ⊆
      Function.support (𝓕 (f : E → ℂ)) + Function.support (𝓕 (g : E → ℂ)) := by
  rw [← SchwartzMap.fourier_coe, glyz_fourier_schwartz_product]
  have he : (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g) : E → ℂ) =
      (𝓕 (f : E → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (𝓕 (g : E → ℂ)) := by
    funext x
    exact SchwartzMap.convolution_apply _ _ _ _
  rw [he]
  exact support_convolution_subset _

/-- A concrete Fourier bump has a strictly positive inverse transform
at the origin. -/
theorem glyzBaseKernel_zero_pos :
    0 < (glyzReproducingKernel (glyzBaseCutoff (E := E) 1 zero_lt_one) 0).re := by
  let b := glyzBaseBump (E := E) 1 zero_lt_one
  have hb : Integrable (b : E → ℝ) := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  have hpos : 0 < ∫ x : E, b x := integral_pos_of_integrable_nonneg_nonzero
    b.continuous hb (fun x => b.nonneg) (x := 0) (by
      rw [b.one_of_mem_closedBall (by simp [b, glyzBaseBump])]
      exact one_ne_zero)
  have he : glyzReproducingKernel (glyzBaseCutoff (E := E) 1 zero_lt_one) 0 =
      ((∫ x : E, b x : ℝ) : ℂ) := by
    rw [glyzReproducingKernel, SchwartzMap.fourierInv_coe, glyz_fourierInv_eq_integral_char]
    simp only [inner_zero_left, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
    change (∫ x : E, (b x : ℂ)) = _
    exact Complex.ofRealCLM.integral_comp_comm hb
  rw [he, Complex.ofReal_re]
  exact hpos

/-- The concrete inverse Fourier bump stays uniformly away from zero
on an actual neighborhood of the origin. -/
theorem exists_glyzBaseKernel_lower_ball :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ x : E, ‖x‖ ≤ ρ →
      c ≤ ‖glyzReproducingKernel (glyzBaseCutoff (E := E) 1 zero_lt_one) x‖ := by
  let K := glyzReproducingKernel (glyzBaseCutoff (E := E) 1 zero_lt_one)
  have hK : 0 < ‖K 0‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hpos := glyzBaseKernel_zero_pos (E := E)
    change 0 < (K 0).re at hpos
    simp [h] at hpos
  have he := (K.continuous.norm.continuousAt).eventually
    (Ioi_mem_nhds (show ‖K 0‖ / 2 < ‖K 0‖ by linarith))
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ρ / 2, ‖K 0‖ / 2, by positivity, by positivity, ?_⟩
  intro x hx
  apply le_of_lt
  exact hball (by simpa only [mem_ball, dist_zero_right] using hx.trans_lt (by linarith))

/-- Positive scalar dilation as a continuous linear equivalence. -/
def glyzScalarEquiv (a : ℝ) (ha : a ≠ 0) : E ≃L[ℝ] E :=
  (LinearEquiv.smulOfNeZero ℝ E a ha).toContinuousLinearEquiv

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem glyzScalarEquiv_apply (a : ℝ) (ha : a ≠ 0) (x : E) :
    glyzScalarEquiv a ha x = a • x := rfl

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem glyzAdjointEquiv_scalar (a : ℝ) (ha : a ≠ 0) (x : E) :
    glyzAdjointEquiv (glyzScalarEquiv a ha) x = a • x := by
  apply ext_inner_right ℝ
  intro y
  rw [glyzAdjointEquiv_inner, glyzScalarEquiv_apply, inner_smul_right,
    inner_smul_left]
  simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- The bump used in the construction has its actual Fourier-variable
support in a fixed radius-two ball. -/
theorem support_glyzBaseCutoff_subset :
    Function.support (glyzBaseCutoff (E := E) 1 zero_lt_one : E → ℂ) ⊆
      closedBall (0 : E) 2 := by
  intro ξ hξ
  have hb : (glyzBaseBump (E := E) 1 zero_lt_one) ξ ≠ 0 := by
    intro h
    apply hξ
    change (((glyzBaseBump (E := E) 1 zero_lt_one) ξ : ℝ) : ℂ) = 0
    rw [h, Complex.ofReal_zero]
  have hmem : ξ ∈ Function.support (glyzBaseBump (E := E) 1 zero_lt_one : E → ℝ) := hb
  rw [(glyzBaseBump (E := E) 1 zero_lt_one).support_eq] at hmem
  apply Metric.ball_subset_closedBall
  simpa only [glyzBaseBump, one_add_one_eq_two] using hmem

/-- A genuine bandlimited Schwartz cutoff which is at least one in norm
on the unit ball. Both the support radius and cutoff are constructed;
neither a localization hypothesis nor an uncertainty principle is assumed. -/
theorem exists_glyz_unit_bandlimited_cutoff :
    ∃ (ψ : SchwartzMap E ℂ) (S : ℝ), 0 < S ∧
      (∀ x : E, ‖x‖ ≤ 1 → 1 ≤ ‖ψ x‖) ∧
      Function.support (𝓕 (ψ : E → ℂ)) ⊆ closedBall (0 : E) S := by
  obtain ⟨ρ, c, hρ, hc, hlower⟩ := exists_glyzBaseKernel_lower_ball (E := E)
  let L := glyzScalarEquiv (E := E) ρ hρ.ne'
  let d := |LinearMap.det L.toLinearMap|
  have hd : 0 < d := abs_pos.mpr (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  let K := glyzReproducingKernel (glyzBaseCutoff (E := E) 1 zero_lt_one)
  let g := glyzSchwartzFrequencyAffine L 0 K
  let ψ : SchwartzMap E ℂ := (d * c)⁻¹ • g
  refine ⟨ψ, 2 * ρ, by positivity, ?_, ?_⟩
  · intro x hx
    have hxρ : ‖ρ • x‖ ≤ ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      nlinarith
    have hg : ‖g x‖ = d * ‖K (ρ • x)‖ := by
      rw [show g = glyzSchwartzFrequencyAffine L 0 K from rfl,
        norm_glyzSchwartzFrequencyAffine]
      simp only [L, glyzAdjointEquiv_scalar, d]
    change 1 ≤ ‖((d * c)⁻¹ : ℝ) • g x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (d * c)⁻¹), hg]
    have h := hlower (ρ • x) hxρ
    change c ≤ ‖K (ρ • x)‖ at h
    calc
      1 = (d * c)⁻¹ * (d * c) := (inv_mul_cancel₀ (mul_pos hd hc).ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hd.le) (by positivity)
  · intro ξ hξ
    have hgξ : ξ ∈ Function.support (𝓕 (g : E → ℂ)) := by
      intro hzero
      apply hξ
      change 𝓕 ((d * c)⁻¹ • g) ξ = 0
      rw [fourier_smul]
      change ((d * c)⁻¹ : ℝ) • 𝓕 (g : E → ℂ) ξ = 0
      rw [hzero, smul_zero]
    rw [show g = glyzSchwartzFrequencyAffine L 0 K from rfl,
      support_fourier_glyzSchwartzFrequencyAffine] at hgξ
    obtain ⟨η, hη, rfl⟩ := hgξ
    have hη' : η ∈ Function.support (glyzBaseCutoff (E := E) 1 zero_lt_one : E → ℂ) := by
      change 𝓕 (𝓕⁻ (glyzBaseCutoff (E := E) 1 zero_lt_one)) η ≠ 0 at hη
      rwa [fourier_fourierInv_eq] at hη
    have hn : ‖η‖ ≤ 2 := by
      simpa only [mem_closedBall, dist_zero_right] using support_glyzBaseCutoff_subset hη'
    simp only [zero_add, L, glyzScalarEquiv_apply, mem_closedBall, dist_zero_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    nlinarith

/-- Uniform, explicitly bandlimited cutoffs on every spatial scale.
The support enlargement constant and decay constant precede the radius. -/
theorem exists_glyz_bandlimited_cutoffs :
    ∃ S : ℝ, 0 < S ∧ ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ R : ℝ, 0 < R → ∃ ψ : SchwartzMap E ℂ,
        (∀ x : E, ‖x‖ ≤ R → 1 ≤ ‖ψ x‖) ∧
        Function.support (𝓕 (ψ : E → ℂ)) ⊆ closedBall (0 : E) (S / R) ∧
        (∀ x : E, ‖ψ x‖ ≤ C * glyzNormWeight A (R⁻¹ • x)) := by
  obtain ⟨φ, S, hS, hφ, hsupport⟩ := exists_glyz_unit_bandlimited_cutoff (E := E)
  refine ⟨S, hS, fun A => ?_⟩
  obtain ⟨C, hC, hdecay⟩ := glyz_schwartz_decay_weight φ A
  refine ⟨C, hC, fun R hR => ?_⟩
  let L := glyzScalarEquiv (E := E) R⁻¹ (inv_ne_zero hR.ne')
  let d := |LinearMap.det L.toLinearMap|
  have hd : 0 < d := abs_pos.mpr (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  let g := glyzSchwartzFrequencyAffine L 0 φ
  let ψ : SchwartzMap E ℂ := d⁻¹ • g
  have hnorm (x : E) : ‖ψ x‖ = ‖φ (R⁻¹ • x)‖ := by
    change ‖(d⁻¹ : ℝ) • g x‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
    rw [show g = glyzSchwartzFrequencyAffine L 0 φ from rfl,
      norm_glyzSchwartzFrequencyAffine]
    simp only [L, glyzAdjointEquiv_scalar]
    change d⁻¹ * (d * ‖φ (R⁻¹ • x)‖) = _
    rw [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]
  refine ⟨ψ, ?_, ?_, fun x => (hnorm x).trans_le (hdecay _)⟩
  · intro x hx
    rw [hnorm]
    apply hφ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    calc
      _ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
      _ = 1 := inv_mul_cancel₀ hR.ne'
  · intro ξ hξ
    have hgξ : ξ ∈ Function.support (𝓕 (g : E → ℂ)) := by
      intro hzero
      apply hξ
      change 𝓕 (d⁻¹ • g) ξ = 0
      rw [fourier_smul]
      change (d⁻¹ : ℝ) • 𝓕 (g : E → ℂ) ξ = 0
      rw [hzero, smul_zero]
    rw [show g = glyzSchwartzFrequencyAffine L 0 φ from rfl,
      support_fourier_glyzSchwartzFrequencyAffine] at hgξ
    obtain ⟨η, hη, rfl⟩ := hgξ
    have hn : ‖η‖ ≤ S := by
      simpa only [mem_closedBall, dist_zero_right] using hsupport hη
    simp only [zero_add, L, glyzScalarEquiv_apply, mem_closedBall, dist_zero_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hn
      (inv_nonneg.mpr hR.le)

/-- Global decoupling applies to actual spatially localized pieces, with
exact frequency-support enlargement. The output is the local weighted
inequality; the global estimate is the lower-dimensional induction input. -/
theorem glyz_local_decoupling_of_bandlimited_cutoff
    {ι : Type*} (s : Finset ι) (f : ι → SchwartzMap E ℂ) (Ω : ι → Set E)
    (ψ : SchwartzMap E ℂ) (R S : ℝ) (p : ℝ) (hp : 0 ≤ p)
    (W : E → ℝ≥0∞) (D : ℝ≥0∞)
    (hf : ∀ i ∈ s, Function.support (𝓕 (f i : E → ℂ)) ⊆ Ω i)
    (hψ : ∀ x : E, ‖x‖ ≤ R → 1 ≤ ‖ψ x‖)
    (hsupp : Function.support (𝓕 (ψ : E → ℂ)) ⊆ closedBall (0 : E) S)
    (hweight : ∀ x, ‖ψ x‖ₑ ^ p ≤ W x)
    (hglobal : ∀ g : ι → SchwartzMap E ℂ,
      (∀ i ∈ s, Function.support (𝓕 (g i : E → ℂ)) ⊆ Ω i + closedBall (0 : E) S) →
      (∫⁻ x, ‖(∑ i ∈ s, g i) x‖ₑ ^ p) ≤ D *
        (∑ i ∈ s, (∫⁻ x, ‖g i x‖ₑ ^ p) ^ (2 / p)) ^ (p / 2)) :
    (∫⁻ x in closedBall (0 : E) R, ‖(∑ i ∈ s, f i) x‖ₑ ^ p) ≤ D *
      (∑ i ∈ s, (∫⁻ x, ‖f i x‖ₑ ^ p * W x) ^ (2 / p)) ^ (p / 2) := by
  classical
  let g : ι → SchwartzMap E ℂ := fun i =>
    SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (f i) ψ
  have hgsupp (i : ι) (hi : i ∈ s) :
      Function.support (𝓕 (g i : E → ℂ)) ⊆ Ω i + closedBall (0 : E) S :=
    (support_fourier_glyz_schwartz_product (f i) ψ).trans (add_subset_add (hf i hi) hsupp)
  have hsum (x : E) : (∑ i ∈ s, g i) x = (∑ i ∈ s, f i) x * ψ x := by
    simp [g, Finset.sum_mul]
  calc
    _ ≤ ∫⁻ x in closedBall (0 : E) R, ‖(∑ i ∈ s, g i) x‖ₑ ^ p := by
      apply setLIntegral_mono' measurableSet_closedBall
      intro x hx
      have hψx : (1 : ℝ≥0∞) ≤ ‖ψ x‖ₑ := by
        simpa only [ENNReal.ofReal_one, ofReal_norm] using ENNReal.ofReal_le_ofReal
          (hψ x (by simpa only [mem_closedBall, dist_zero_right] using hx))
      rw [hsum, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hp]
      exact le_mul_of_one_le_right' (by simpa using ENNReal.rpow_le_rpow hψx hp)
    _ ≤ ∫⁻ x, ‖(∑ i ∈ s, g i) x‖ₑ ^ p := lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ D * (∑ i ∈ s, (∫⁻ x, ‖g i x‖ₑ ^ p) ^ (2 / p)) ^ (p / 2) := hglobal g hgsupp
    _ ≤ _ := by
      apply mul_le_mul_right
      apply ENNReal.rpow_le_rpow _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      apply ENNReal.rpow_le_rpow _ (by positivity)
      apply lintegral_mono
      intro x
      change ‖f i x * ψ x‖ₑ ^ p ≤ _
      rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hp]
      exact mul_le_mul_right (hweight x) _

/-- Uniform local weighted decoupling on every ball, obtained using the
constructed cutoff family. No spatial-localization assumption remains. -/
theorem exists_glyz_global_to_local_decoupling (A : ℕ) :
    ∃ S C : ℝ, 0 < S ∧ 0 < C ∧ ∀ (R : ℝ), 0 < R →
      ∀ (p : ℝ), 0 ≤ p → ∀ (ι : Type*) (s : Finset ι)
      (f : ι → SchwartzMap E ℂ) (Ω : ι → Set E) (D : ℝ≥0∞),
      (∀ i ∈ s, Function.support (𝓕 (f i : E → ℂ)) ⊆ Ω i) →
      (∀ g : ι → SchwartzMap E ℂ,
        (∀ i ∈ s, Function.support (𝓕 (g i : E → ℂ)) ⊆
          Ω i + closedBall (0 : E) (S / R)) →
        (∫⁻ x, ‖(∑ i ∈ s, g i) x‖ₑ ^ p) ≤ D *
          (∑ i ∈ s, (∫⁻ x, ‖g i x‖ₑ ^ p) ^ (2 / p)) ^ (p / 2)) →
      (∫⁻ x in closedBall (0 : E) R, ‖(∑ i ∈ s, f i) x‖ₑ ^ p) ≤ D *
        (∑ i ∈ s, (∫⁻ x, ‖f i x‖ₑ ^ p *
          ENNReal.ofReal (C * glyzNormWeight A (R⁻¹ • x)) ^ p) ^ (2 / p)) ^ (p / 2) := by
  obtain ⟨S, hS, hcut⟩ := exists_glyz_bandlimited_cutoffs (E := E)
  obtain ⟨C, hC, hcut⟩ := hcut A
  refine ⟨S, C, hS, hC, fun R hR p hp ι s f Ω D hf hglobal => ?_⟩
  obtain ⟨ψ, hlower, hsupp, hdecay⟩ := hcut R hR
  exact glyz_local_decoupling_of_bandlimited_cutoff s f Ω ψ R (S / R) p hp
    (fun x => ENNReal.ofReal (C * glyzNormWeight A (R⁻¹ • x)) ^ p) D hf hlower hsupp
    (fun x => ENNReal.rpow_le_rpow (by
      simpa only [ofReal_norm] using (ENNReal.ofReal_le_ofReal (hdecay x))) hp) hglobal

/-- Homogeneity of the finite square-sum expression in the actual
nonnegative p-th power integrals. -/
theorem glyz_power_square_sum_mul {ι : Type*} (s : Finset ι)
    (a : ι → ℝ≥0∞) (c : ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (∑ i ∈ s, (c * a i) ^ (2 / p)) ^ (p / 2) =
      c * (∑ i ∈ s, a i ^ (2 / p)) ^ (p / 2) := by
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 2 / p)]
  rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
  have he : (2 / p) * (p / 2) = (1 : ℝ) := by field_simp
  rw [he, ENNReal.rpow_one]

/-- Canonical polynomial-weight form of the localization estimate.
The loss C is uniform in the radius, every frequency box, every finite
family, and the global decoupling constant. -/
theorem exists_glyz_global_to_weighted_local_decoupling (A : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    ∃ S C : ℝ, 0 < S ∧ 0 < C ∧ ∀ (R : ℝ), 0 < R →
      ∀ (ι : Type*) (s : Finset ι) (f : ι → SchwartzMap E ℂ)
      (Ω : ι → Set E) (D : ℝ≥0∞),
      (∀ i ∈ s, Function.support (𝓕 (f i : E → ℂ)) ⊆ Ω i) →
      (∀ g : ι → SchwartzMap E ℂ,
        (∀ i ∈ s, Function.support (𝓕 (g i : E → ℂ)) ⊆
          Ω i + closedBall (0 : E) (S / R)) →
        (∫⁻ x, ‖(∑ i ∈ s, g i) x‖ₑ ^ p) ≤ D *
          (∑ i ∈ s, (∫⁻ x, ‖g i x‖ₑ ^ p) ^ (2 / p)) ^ (p / 2)) →
      (∫⁻ x in closedBall (0 : E) R, ‖(∑ i ∈ s, f i) x‖ₑ ^ p) ≤
        D * ENNReal.ofReal C *
          (∑ i ∈ s, (∫⁻ x, ‖f i x‖ₑ ^ p *
            ENNReal.ofReal (glyzNormWeight A (R⁻¹ • x))) ^ (2 / p)) ^ (p / 2) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  obtain ⟨S, hS, hcut⟩ := exists_glyz_bandlimited_cutoffs (E := E)
  obtain ⟨C, hC, hcut⟩ := hcut A
  refine ⟨S, C ^ p, hS, Real.rpow_pos_of_pos hC _, fun R hR ι s f Ω D hf hglobal => ?_⟩
  obtain ⟨ψ, hlower, hsupp, hdecay⟩ := hcut R hR
  let c := ENNReal.ofReal C ^ p
  let w : E → ℝ≥0∞ := fun x => ENNReal.ofReal (glyzNormWeight A (R⁻¹ • x))
  have hc : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top
  have hweight (x : E) : ‖ψ x‖ₑ ^ p ≤ c * w x := by
    have hw1 : w x ≤ 1 := by
      apply (ENNReal.ofReal_le_one).mpr
      change (max (1 : ℝ) ‖R⁻¹ • x‖ ^ A)⁻¹ ≤ 1
      apply inv_le_one_of_one_le₀
      exact one_le_pow₀ (le_max_left _ _)
    calc
      _ ≤ ENNReal.ofReal (C * glyzNormWeight A (R⁻¹ • x)) ^ p :=
        ENNReal.rpow_le_rpow (by
          simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hdecay x)) hp0.le
      _ = c * w x ^ p := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
      _ ≤ _ := mul_le_mul_right (ENNReal.rpow_le_self_of_le_one hw1 hp) _
  have h := glyz_local_decoupling_of_bandlimited_cutoff s f Ω ψ R (S / R) p hp0.le
    (fun x => c * w x) D hf hlower hsupp hweight hglobal
  have hi (i : ι) : (∫⁻ x, ‖f i x‖ₑ ^ p * (c * w x)) =
      c * ∫⁻ x, ‖f i x‖ₑ ^ p * w x := by
    simp_rw [mul_left_comm (‖f i _‖ₑ ^ p) c]
    exact lintegral_const_mul' _ _ hc
  simp_rw [hi] at h
  rw [glyz_power_square_sum_mul s _ c hp0] at h
  have he : c = ENNReal.ofReal (C ^ p) := ENNReal.ofReal_rpow_of_nonneg hC.le hp0.le
  simpa only [he, mul_assoc, w] using h

/-- Normalize an actual local weighted inequality by the volume of the
physical ball. The same normalization enters every weighted piece and
cancels by the square-sum homogeneity. -/
theorem glyz_normalize_local_decoupling {ι : Type*} (s : Finset ι)
    (f : ι → SchwartzMap E ℂ) {R p : ℝ} (hR : 0 < R) (hp : 0 < p)
    (w : E → ℝ≥0∞) (D : ℝ≥0∞)
    (hlocal : (∫⁻ x in closedBall (0 : E) R, ‖(∑ i ∈ s, f i) x‖ₑ ^ p) ≤ D *
      (∑ i ∈ s, (∫⁻ x, ‖f i x‖ₑ ^ p * w x) ^ (2 / p)) ^ (p / 2)) :
    (∫⁻ x, ‖(∑ i ∈ s, f i) x‖ₑ ^ p ∂glyzBallMeasure E R) ≤ D *
      (∑ i ∈ s, (∫⁻ x, ‖f i x‖ₑ ^ p *
        ((volume (closedBall (0 : E) R))⁻¹ * w x)) ^ (2 / p)) ^ (p / 2) := by
  let c : ℝ≥0∞ := (volume (closedBall (0 : E) R))⁻¹
  have hc : c ≠ ⊤ := ENNReal.inv_ne_top.mpr (measure_closedBall_pos volume (0 : E) hR).ne'
  have hi (i : ι) : (∫⁻ x, ‖f i x‖ₑ ^ p * (c * w x)) =
      c * ∫⁻ x, ‖f i x‖ₑ ^ p * w x := by
    simp_rw [mul_left_comm (‖f i _‖ₑ ^ p) c]
    exact lintegral_const_mul' _ _ hc
  change (∫⁻ x, ‖(∑ i ∈ s, f i) x‖ₑ ^ p ∂glyzBallMeasure E R) ≤ D *
    (∑ i ∈ s, (∫⁻ x, ‖f i x‖ₑ ^ p * (c * w x)) ^ (2 / p)) ^ (p / 2)
  simp_rw [hi]
  rw [glyz_power_square_sum_mul s _ c hp, glyzBallMeasure, lintegral_smul_measure, smul_eq_mul]
  change c * _ ≤ D * (c * _)
  calc
    _ ≤ c * (D * (∑ i ∈ s, (∫⁻ x, ‖f i x‖ₑ ^ p * w x) ^ (2 / p)) ^ (p / 2)) :=
      mul_le_mul_right hlocal c
    _ = _ := by ring

/-- The actual localization support enlargement is absorbed at the
smallest side of a derivative-scaled curve box. -/
theorem glyz_scaled_box_add_ball_subset {l : ℕ}
    (L : GlyzSpace l ≃L[ℝ] GlyzSpace l) {δ C R S : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C)
    (hL : ‖L.symm.toContinuousLinearMap‖ ≤ C) (a : GlyzSpace l) :
    glyzFrequencyBox (glyzScaledFrame L δ hδ) a R +
        closedBall (0 : GlyzSpace l) (S * δ ^ l) ⊆
      glyzFrequencyBox (glyzScaledFrame L δ hδ) a (R + C * S) := by
  rintro ξ ⟨η, hη, z, hz, rfl⟩
  let Q := (EuclideanSpace.equiv (Fin l) ℝ).toContinuousLinearMap.comp
    (glyzScaledFrame L δ hδ).symm.toContinuousLinearMap
  change ‖Q (η + z - a)‖ ≤ R + C * S
  change ‖Q (η - a)‖ ≤ R at hη
  have hz' : ‖z‖ ≤ S * δ ^ l := by simpa only [mem_closedBall, dist_zero_right] using hz
  have he : Q (η + z - a) = Q (η - a) + Q z := by
    rw [← map_add]
    congr 1
    abel
  have hQ : ‖Q z‖ ≤ C * S := by
    calc
      _ ≤ (δ ^ l)⁻¹ * (C * ‖z‖) :=
        norm_glyzScaledFrame_symm_coordinates_le L hδ hδ1 hC hL z
      _ ≤ (δ ^ l)⁻¹ * (C * (S * δ ^ l)) := by gcongr
      _ = C * S := by field_simp
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hη hQ)

/-- Fourier support of a localized curve piece remains in a uniformly
enlarged actual curve box. -/
theorem support_fourier_localized_glyz_scaled_box {l : ℕ}
    (L : GlyzSpace l ≃L[ℝ] GlyzSpace l) {δ C R S : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C)
    (hL : ‖L.symm.toContinuousLinearMap‖ ≤ C)
    (a : GlyzSpace l) (f ψ : SchwartzMap (GlyzSpace l) ℂ)
    (hf : Function.support (𝓕 (f : GlyzSpace l → ℂ)) ⊆
      glyzFrequencyBox (glyzScaledFrame L δ hδ) a R)
    (hψ : Function.support (𝓕 (ψ : GlyzSpace l → ℂ)) ⊆
      closedBall (0 : GlyzSpace l) (S * δ ^ l)) :
    Function.support (𝓕 ((SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f ψ) :
      GlyzSpace l → ℂ)) ⊆ glyzFrequencyBox (glyzScaledFrame L δ hδ) a (R + C * S) :=
  (support_fourier_glyz_schwartz_product f ψ).trans
    ((add_subset_add hf hψ).trans (glyz_scaled_box_add_ball_subset L hδ hδ1 hC hL a))

/-- Corollary 3.7's support localization for actual derivative-scaled
boxes. The scale is the reciprocal of the shortest Fourier side.
A global estimate for uniformly enlarged boxes suffices. -/
theorem exists_glyz_scaled_boxes_local_decoupling (l A : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    ∃ S C : ℝ, 0 < S ∧ 0 < C ∧
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (K T : ℝ), 0 ≤ K → ∀ (ι : Type*) (s : Finset ι)
      (L : ι → GlyzSpace l ≃L[ℝ] GlyzSpace l) (a : ι → GlyzSpace l)
      (f : ι → SchwartzMap (GlyzSpace l) ℂ) (D : ℝ≥0∞),
      (∀ i ∈ s, ‖(L i).symm.toContinuousLinearMap‖ ≤ K) →
      (∀ i ∈ s, Function.support (𝓕 (f i : GlyzSpace l → ℂ)) ⊆
        glyzFrequencyBox (glyzScaledFrame (L i) δ hδ) (a i) T) →
      (∀ g : ι → SchwartzMap (GlyzSpace l) ℂ,
        (∀ i ∈ s, Function.support (𝓕 (g i : GlyzSpace l → ℂ)) ⊆
          glyzFrequencyBox (glyzScaledFrame (L i) δ hδ) (a i) (T + K * S)) →
        (∫⁻ x, ‖(∑ i ∈ s, g i) x‖ₑ ^ p) ≤ D *
          (∑ i ∈ s, (∫⁻ x, ‖g i x‖ₑ ^ p) ^ (2 / p)) ^ (p / 2)) →
      (∫⁻ x in closedBall (0 : GlyzSpace l) (δ ^ l)⁻¹, ‖(∑ i ∈ s, f i) x‖ₑ ^ p) ≤
        D * ENNReal.ofReal C *
          (∑ i ∈ s, (∫⁻ x, ‖f i x‖ₑ ^ p *
            ENNReal.ofReal (glyzNormWeight A ((δ ^ l) • x))) ^ (2 / p)) ^ (p / 2) := by
  obtain ⟨S, C, hS, hC, hlocal⟩ :=
    exists_glyz_global_to_weighted_local_decoupling (E := GlyzSpace l) A hp
  refine ⟨S, C, hS, hC, fun δ hδ hδ1 K T hK ι s L a f D hL hf hglobal => ?_⟩
  have h := hlocal ((δ ^ l)⁻¹) (by positivity) ι s f
    (fun i => glyzFrequencyBox (glyzScaledFrame (L i) δ hδ) (a i) T) D hf ?_
  · simpa only [inv_inv] using h
  · intro g hg
    apply hglobal g
    intro i hi
    apply (hg i hi).trans
    rw [div_inv_eq_mul]
    exact glyz_scaled_box_add_ball_subset (L i) hδ hδ1 hK (hL i hi) (a i)

end PlanarNikodym
