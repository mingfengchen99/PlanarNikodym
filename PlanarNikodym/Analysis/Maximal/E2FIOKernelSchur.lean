import PlanarNikodym.Analysis.Maximal.E2FIOPositiveSchur
import PlanarNikodym.Analysis.Fourier.GlyzNormWeightMass

/-! Schur bounds for actual complex integral operators, and exact
semiclassical decay of the mass of a polynomial kernel majorant. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace PlanarNikodym
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem e2_complex_kernel_l2_schur (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] {K : X → Y → ℂ} {f : Y → ℂ}
    (hK : Measurable (Function.uncurry K)) (hf : Measurable f)
    (A B : ℝ≥0∞) (hrow : ∀ x, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A)
    (hcol : ∀ y, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B) :
    (∫⁻ x, ‖∫ y, K x y * f y ∂ν‖ₑ ^ (2 : ℕ) ∂μ) ≤
      A * B * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℕ) ∂ν := by
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, ‖K x y‖ₑ * ‖f y‖ₑ ∂ν) ^ (2 : ℕ) ∂μ := by
      apply lintegral_mono
      intro x
      have hh := enorm_integral_le_lintegral_enorm (μ := ν) (fun y => K x y * f y)
      simp only [enorm_mul] at hh
      exact pow_le_pow_left₀ zero_le hh 2
    _ ≤ _ := e2_positive_kernel_l2_schur μ ν (κ := fun x y => ‖K x y‖ₑ)
      (f := fun y => ‖f y‖ₑ) hK.enorm hf.enorm A B hrow hcol

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def e2FIODecayMass (N : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((r ^ Module.finrank ℝ E)⁻¹) *
    ∫⁻ z : E, ENNReal.ofReal (glyzNormWeight N z)

theorem e2FIODecayMass_ne_top {N : ℕ} (hN : Module.finrank ℝ E < N) (r : ℝ) :
    e2FIODecayMass (E := E) N r ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top (glyzNormWeight_lintegral_ne_top hN)

theorem e2_fio_decay_row_mass (N : ℕ) {r : ℝ} (hr : 0 < r) (x : E) :
    (∫⁻ y : E, ENNReal.ofReal (glyzNormWeight N (r • (x - y)))) =
      e2FIODecayMass (E := E) N r := by
  rw [lintegral_sub_left_eq_self (fun y : E => ENNReal.ofReal (glyzNormWeight N (r • y))) x,
    glyz_lintegral_comp_smul (fun z : E => ENNReal.ofReal (glyzNormWeight N z)) hr.ne', abs_of_pos (by positivity)]
  rfl

theorem e2_complex_kernel_l2_schur_of_decay {K : E → E → ℂ} {f : E → ℂ}
    (hK : Measurable (Function.uncurry K)) (hf : Measurable f)
    (N : ℕ) {r : ℝ} (hr : 0 < r) (C : ℝ≥0∞)
    (hdecay : ∀ x y, ‖K x y‖ₑ ≤
      C * ENNReal.ofReal (glyzNormWeight N (r • (x - y)))) :
    (∫⁻ x : E, ‖∫ y : E, K x y * f y‖ₑ ^ (2 : ℕ)) ≤
      (C * e2FIODecayMass (E := E) N r) ^ (2 : ℕ) *
        ∫⁻ y : E, ‖f y‖ₑ ^ (2 : ℕ) := by
  have hm : Measurable (fun y : E => ENNReal.ofReal (glyzNormWeight N (r • y))) :=
    ENNReal.measurable_ofReal.comp ((continuous_glyzNormWeight N).comp
      (continuous_const.smul continuous_id)).measurable
  have hrows (x : E) : (∫⁻ y : E, ‖K x y‖ₑ) ≤ C * e2FIODecayMass (E := E) N r := by
    calc
      _ ≤ ∫⁻ y : E, C * ENNReal.ofReal (glyzNormWeight N (r • (x - y))) :=
        lintegral_mono (hdecay x)
      _ = _ := by rw [lintegral_const_mul C (show Measurable (fun y : E => ENNReal.ofReal (glyzNormWeight N (r • (x - y)))) from hm.comp (measurable_const.sub measurable_id)),
        e2_fio_decay_row_mass N hr]
  have hc (y : E) : (∫⁻ x : E, ‖K x y‖ₑ) ≤ C * e2FIODecayMass (E := E) N r := by
    calc
      _ ≤ ∫⁻ x : E, C * ENNReal.ofReal (glyzNormWeight N (r • (x - y))) :=
        lintegral_mono (fun x => hdecay x y)
      _ = _ := by
        rw [lintegral_const_mul C (show Measurable (fun x : E => ENNReal.ofReal (glyzNormWeight N (r • (x - y)))) from hm.comp (measurable_id.sub measurable_const)),
          lintegral_sub_right_eq_self (fun z : E => ENNReal.ofReal (glyzNormWeight N (r • z))) y, glyz_lintegral_comp_smul (fun z : E => ENNReal.ofReal (glyzNormWeight N z)) hr.ne',
          abs_of_pos (by positivity)]
        rfl
  simpa only [pow_two] using e2_complex_kernel_l2_schur volume volume hK hf
    (C * e2FIODecayMass (E := E) N r) (C * e2FIODecayMass (E := E) N r) hrows hc

end PlanarNikodym
