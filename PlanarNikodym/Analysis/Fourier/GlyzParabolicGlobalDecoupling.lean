import PlanarNikodym.Analysis.Fourier.GlyzParabolicGlobalRegularity
import PlanarNikodym.Analysis.Fourier.GlyzNormWeightGlobalization

/-! Whole-space decoupling for the actual compact parabolic extension.
The spatial cutoff is removed on each unit ball, centers are integrated
by Tonelli, and the error volume is controlled by the actual output
support. Constants precede every parabolic scale and center. -/
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ContDiff ENNReal NNReal BigOperators
namespace PlanarNikodym

def glyzParabolicGlobalExtension {d k : ℕ}
    (A : GlyzParabolicSymbolVariables d k → ℂ)
    (H : GlyzParabolicSymbolVariables d k → ℝ)
    (q : ℝ × Aux (d + 2)) (δ : ℝ) (hδ : δ ≠ 0)
    (α R : ℝ) (g : Plane → ℂ) (x : GlyzConeSpace k) : ℂ :=
  polynomialExtension (glyzCompactParabolicAmplitude A H q δ hδ α)
    g R (glyzMomentConeCoefficientEquiv k x)

section Cutoff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem glyz_cutoff_translate_ball {ι : Type*} (I : Finset ι)
    (f : ι → E → ℂ) (χ : E → ℂ)
    (hχ : ∀ x ∈ closedBall (0 : E) 1, χ x = 1) (a : E) (p : ℝ) :
    (∫⁻ x in closedBall (0 : E) 1, ‖∑ i ∈ I, χ x * f i (x + a)‖ₑ ^ p) =
      ∫⁻ x in closedBall a 1, ‖∑ i ∈ I, f i x‖ₑ ^ p := by
  rw [← glyz_lintegral_closedBall_translate a 1 (fun x => ‖∑ i ∈ I, f i x‖ₑ ^ p)]
  apply setLIntegral_congr_fun measurableSet_closedBall
  intro x hx
  simp only [hχ x hx, one_mul]

theorem glyz_cutoff_translate_weight_le (f : E → ℂ) (χ : E → ℂ)
    (hχ : ∀ x, ‖χ x‖ ≤ 1) (a : E) {p : ℝ} (hp : 0 ≤ p) (w : E → ℝ≥0∞) :
    (∫⁻ x, ‖χ x * f (x + a)‖ₑ ^ p * w x) ≤
      ∫⁻ x, ‖f x‖ₑ ^ p * w (x - a) := by
  rw [← glyz_lintegral_translate_weight a (fun x => ‖f x‖ₑ ^ p) w]
  apply lintegral_mono
  intro x
  apply mul_le_mul_left
  apply ENNReal.rpow_le_rpow _ hp
  rw [enorm_mul]
  have hc : ‖χ x‖ₑ ≤ 1 := by
    simpa only [← ofReal_norm, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hχ x)
  exact mul_le_of_le_one_left zero_le hc

theorem glyz_unit_closedBall_volume_ratio {r : ℝ} (hr : 0 < r) :
    volume (closedBall (0 : E) r) / volume (closedBall (0 : E) 1) =
      ENNReal.ofReal (r ^ Module.finrank ℝ E) := by
  rw [addHaar_closedBall' volume (0 : E) hr.le]
  exact ENNReal.mul_div_cancel_right
    (measure_closedBall_pos volume (0 : E) zero_lt_one).ne' measure_closedBall_lt_top.ne

end Cutoff

theorem glyz_parabolic_global_lp_L1_error (d k W M : ℕ) (hk : 0 < k)
    (hW : Module.finrank ℝ (GlyzConeSpace k) < W)
    (A : GlyzParabolicSymbolVariables d k → ℂ)
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (H : GlyzParabolicSymbolVariables d k → ℝ)
    (hH : ContDiff ℝ ∞ H) (hcH : HasCompactSupport H)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent k ≤ p)
    {ε rmin rmax : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) :
    ∃ C D L Cg : ℝ, 0 < C ∧ 0 ≤ D ∧ 0 < L ∧ 0 < Cg ∧
      ∀ (q : ℝ × Aux (d + 2)) (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (α : ℝ) (N : ℕ) (R T : ℝ), 0 < R → 0 < T →
      1 + 2 * ((1 + |α|) * T) ≤
        (rmin / 4) * (R / (2 * Real.pi)) * glyzDyadicScale N ^ k →
      ∀ (I : Finset ℕ) (J : ℕ → Set ℝ) (g : ℕ → Plane → ℂ),
      I ⊆ Finset.range (2 ^ N) → (∀ i, IsCompact (J i)) →
      (∀ i ∈ I, J i ⊆ Icc (0 : ℝ) 1) →
      (∀ i ∈ I, ∀ t ∈ J i, |t - glyzDyadicCenter N i| ≤ glyzDyadicScale N) →
      (∀ i, Integrable (g i)) →
      (∀ i ∈ I, Function.support (g i) ⊆ J i ×ˢ Icc rmin rmax) →
      let P := fun i => glyzParabolicGlobalExtension A H q δ hδ.ne' α R (g i)
      let e := fun i => (D * (1 + |α|) ^ (volume : Measure (GlyzConeSpace k)).integrablePower *
        (T⁻¹) ^ M) * ∫ y, ‖g i y‖
      let B : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (p : ℝ)
      let Q := ENNReal.ofReal (C * (2 : ℝ) ^
        (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N))
      let mass := ∫⁻ x : GlyzConeSpace k, ENNReal.ofReal (glyzNormWeight W x)
      let unitMass := volume (closedBall (0 : GlyzConeSpace k) 1)
      (∫⁻ x, ‖∑ i ∈ I, P i x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal Cg * (B * Q * B) * ∑ i ∈ I, (∫⁻ x, ‖P i x‖ₑ ^ (p : ℝ)) +
        (B * (Q * B * ((∑ i ∈ I, ENNReal.ofReal (e i) ^ (p : ℝ)) * mass) +
          ENNReal.ofReal (∑ i ∈ I, e i) ^ (p : ℝ) * unitMass)) *
            ENNReal.ofReal (((δ ^ k)⁻¹ * L + 1) ^ Module.finrank ℝ (GlyzConeSpace k)) := by
  obtain ⟨χr, V, hχr, hcχr, hχrange, _, hBV, hχone, _⟩ :=
    exists_compact_smooth_cutoff (K := closedBall (0 : GlyzConeSpace k) 1)
      (S := univ) (isCompact_closedBall _ _) isOpen_univ (subset_univ _)
  let χ : GlyzConeSpace k → ℂ := fun x => (χr x : ℂ)
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp hχr
  have hcχ : HasCompactSupport χ := hcχr.comp_left (g := Complex.ofRealCLM) rfl
  have hχb (x : GlyzConeSpace k) : ‖χ x‖ ≤ 1 := by
    simpa only [χ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχrange x).1]
      using (hχrange x).2
  have hχ1 (x : GlyzConeSpace k) (hx : x ∈ closedBall 0 1) : χ x = 1 := by
    simp only [χ, hχone x (hBV hx), Complex.ofReal_one]
  obtain ⟨C, D, hC, hD, hb⟩ := glyz_centered_parabolic_local_lp_L1_error d k W M hk
    χ hχ hcχ A hA hcA H hH hcH hp hε hrmin (rmax := rmax)
  obtain ⟨L, hL, hs⟩ := exists_glyz_compact_parabolic_cone_output_bound A hcA
    (glyzMomentConeCoefficientEquiv k)
  obtain ⟨Cg, hCg, hglob⟩ :=
    exists_glyz_normWeight_globalization_constant (E := GlyzConeSpace k) hW
  refine ⟨C, D, L, Cg, hC, hD, hL, hCg, ?_⟩
  intro q δ hδ hδ1 α N R T hR hT hscale I J g hI hJ hJu hJc hg hgs
  let P := fun i => glyzParabolicGlobalExtension A H q δ hδ.ne' α R (g i)
  let err := fun i => (D * (1 + |α|) ^ (volume : Measure (GlyzConeSpace k)).integrablePower *
    (T⁻¹) ^ M) * ∫ y, ‖g i y‖
  let B : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (p : ℝ)
  let Q := ENNReal.ofReal (C * (2 : ℝ) ^
    (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N))
  let w := fun x : GlyzConeSpace k => ENNReal.ofReal (glyzNormWeight W x)
  let error : ℝ≥0∞ := B * (Q * B * ((∑ i ∈ I, ENNReal.ofReal (err i) ^ (p : ℝ)) *
    ∫⁻ x, w x) + ENNReal.ofReal (∑ i ∈ I, err i) ^ (p : ℝ) *
      volume (closedBall (0 : GlyzConeSpace k) 1))
  have hpc : ∀ i, Continuous (P i) := fun i =>
    continuous_glyz_global_parabolic A hA hcA H hH q hδ hδ1 α R (g i) (hg i)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (one_le_glyzCriticalNNExponent hk).trans hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hsup : Function.support (fun x => ‖∑ i ∈ I, P i x‖ₑ ^ (p : ℝ)) ⊆
      closedBall (0 : GlyzConeSpace k) ((δ ^ k)⁻¹ * L) := by
    intro x hx
    by_contra hn
    have hz (i : ℕ) : P i x = 0 := by
      by_contra hi
      exact hn (hs H q δ hδ hδ1 α R (g i) hi)
    exact hx (by simp only [hz, Finset.sum_const_zero, enorm_zero, ENNReal.zero_rpow_of_pos hp0])
  have hlocal (a : GlyzConeSpace k) :
      (∫⁻ x in closedBall a 1, ‖∑ i ∈ I, P i x‖ₑ ^ (p : ℝ)) ≤
        (B * Q * B) * ∑ i ∈ I, (∫⁻ x, ‖P i x‖ₑ ^ (p : ℝ) * w (x - a)) + error := by
    let u : GlyzLocalizedParabolicParameters d k :=
      ⟨δ, hδ, hδ1, q, glyzMomentConeCoefficientEquiv k a, 1, by norm_num⟩
    have hh := hb u rfl α N R T hR hT hscale I J g hI hJ hJu hJc hg hgs
    have he (i : ℕ) (x : GlyzConeSpace k) :
        χ x * polynomialExtension
          (glyzCompactParabolicAmplitude A H u.frozen u.δ u.δ_pos.ne' α)
          (g i) R (u.center + glyzMomentConeCoefficientEquiv k x) = χ x * P i (x + a) := by
      simp only [P, glyzParabolicGlobalExtension, u, map_add, add_comm]
    simp only [he] at hh
    rw [glyz_cutoff_translate_ball I P χ hχ1 a (p : ℝ)] at hh
    apply hh.trans
    have hweighted : (∑ i ∈ I, ∫⁻ x, ‖χ x * P i (x + a)‖ₑ ^ (p : ℝ) * w x) ≤
        ∑ i ∈ I, ∫⁻ x, ‖P i x‖ₑ ^ (p : ℝ) * w (x - a) :=
      Finset.sum_le_sum (fun i _ => glyz_cutoff_translate_weight_le (P i) χ hχb a hp0.le w)
    change B * (Q * (B * (_ + _)) + _) ≤ _
    calc
      _ ≤ B * (Q * (B * ((∑ i ∈ I, ∫⁻ x, ‖P i x‖ₑ ^ (p : ℝ) * w (x - a)) +
          (∑ i ∈ I, ENNReal.ofReal (err i) ^ (p : ℝ)) * ∫⁻ x, w x)) +
          ENNReal.ofReal (∑ i ∈ I, err i) ^ (p : ℝ) *
            volume (closedBall (0 : GlyzConeSpace k) 1)) := by gcongr
      _ = _ := by dsimp only [error]; ring
  have hglo := hglob I
    (fun x => ‖∑ i ∈ I, P i x‖ₑ ^ (p : ℝ)) (fun i x => ‖P i x‖ₑ ^ (p : ℝ))
    ((continuous_finsetSum I (fun i _ => hpc i)).enorm.measurable.pow_const _)
    (fun i _ => (hpc i).enorm.measurable.pow_const _)
    ((δ ^ k)⁻¹ * L) 1 zero_lt_one hsup (B * Q * B) error
    (fun a _ => by simpa only [inv_one, one_smul] using hlocal a)
  rw [glyz_unit_closedBall_volume_ratio (by positivity : 0 < (δ ^ k)⁻¹ * L + 1)] at hglo
  exact hglo

end PlanarNikodym
