import PlanarNikodym.Analysis.Fourier.GlyzNormWeightMass
import PlanarNikodym.Analysis.Maximal.E2FIOBilinearSchur
/-! The polynomial Schur majorant has finite mass and exact r⁻²
scaling for the actual max norm and product volume on the input plane.
The proof uses finite-dimensional normed-space Haar scaling directly. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
set_option autoImplicit false
namespace PlanarNikodym

theorem e2_integrable_plane_normWeight {N : ℕ} (hN : 2 < N) :
    Integrable (glyzNormWeight (E := Plane) N) := by
  have hr : (Module.finrank ℝ Plane : ℝ) < (N : ℝ) := by
    simpa [Plane] using (show (2 : ℝ) < (N : ℝ) by exact_mod_cast hN)
  apply ((integrable_one_add_norm (E := Plane) (μ := volume) hr).const_mul ((2 : ℝ)^N)).mono'
    (continuous_glyzNormWeight N).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x =>
    (abs_of_pos (glyzNormWeight_pos N x)).trans_le (glyzNormWeight_le_japanese N x)

theorem e2_plane_lintegral_comp_smul (W : Plane → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ x : Plane, W (r • x)) = ENNReal.ofReal |(r^2)⁻¹| * ∫⁻ x : Plane, W x := by
  let e : Plane ≃ᵐ Plane := (Homeomorph.smul (isUnit_iff_ne_zero.mpr hr).unit).toMeasurableEquiv
  have h := lintegral_map_equiv W e (μ := (volume : Measure Plane))
  change (∫⁻ x, W x ∂Measure.map (fun y : Plane => r • y) volume) = ∫⁻ x, W (r • x) at h
  rw [Measure.map_addHaar_smul volume hr, lintegral_smul_measure, smul_eq_mul] at h
  simpa [Plane] using h.symm

theorem e2_plane_lintegral_normWeight_smul_sub (N : ℕ) {r : ℝ} (hr : 0 < r) (a : Plane) :
    (∫⁻ x : Plane, ENNReal.ofReal (glyzNormWeight N (r • (x-a)))) =
      ENNReal.ofReal ((r^2)⁻¹) * ∫⁻ x : Plane, ENNReal.ofReal (glyzNormWeight N x) := by
  rw [lintegral_sub_right_eq_self (fun x : Plane => ENNReal.ofReal (glyzNormWeight N (r • x))) a,
    e2_plane_lintegral_comp_smul (fun x : Plane => ENNReal.ofReal (glyzNormWeight N x)) hr.ne',
    abs_of_pos (inv_pos.mpr (pow_pos hr _))]

theorem e2_plane_normWeight_lintegral_ne_top {N : ℕ} (hN : 2 < N) :
    (∫⁻ x : Plane, ENNReal.ofReal (glyzNormWeight N x)) ≠ ⊤ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (e2_integrable_plane_normWeight hN)
    (Filter.Eventually.of_forall fun x => (glyzNormWeight_pos N x).le)]
  exact ENNReal.ofReal_ne_top

theorem e2_plane_weight_bilinear_schur (N : ℕ) (r : ℝ) (hr : 0 < r)
    {f : Plane → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : Plane, ∫⁻ y : Plane,
      ENNReal.ofReal (glyzNormWeight N (r • (y-x))) * (f x * f y)) ≤
      (ENNReal.ofReal ((r^2)⁻¹) * ∫⁻ x : Plane, ENNReal.ofReal (glyzNormWeight N x)) *
        ∫⁻ x : Plane, f x ^ (2 : ℕ) := by
  apply e2_positive_kernel_bilinear_schur volume
    (κ := fun x y : Plane => ENNReal.ofReal (glyzNormWeight N (r • (y-x))))
    (ENNReal.measurable_ofReal.comp ((continuous_glyzNormWeight N).comp
      (show Continuous (fun z : Plane × Plane => r • (z.2-z.1)) from
        continuous_const.smul (continuous_snd.sub continuous_fst))).measurable) hf
  · intro x
    exact (e2_plane_lintegral_normWeight_smul_sub N hr x).le
  · intro y
    have he : (fun x : Plane => ENNReal.ofReal (glyzNormWeight N (r • (y-x)))) =
        fun x : Plane => ENNReal.ofReal (glyzNormWeight N (r • (x-y))) := by
      funext x
      simp only [glyzNormWeight, norm_smul, norm_sub_rev]
    rw [he]
    exact (e2_plane_lintegral_normWeight_smul_sub N hr y).le

end PlanarNikodym
