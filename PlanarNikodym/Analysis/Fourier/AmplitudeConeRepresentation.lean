import PlanarNikodym.Analysis.Fourier.JointAmplitudeFourier
import PlanarNikodym.Analysis.Fourier.LinearConeRepresentation

/-! Absolute Fubini turns the actual smooth variable amplitude into an
integrable superposition of unitary modulations of the genuine cone
extension.  The scalar Fourier coefficients are constructed from the
given amplitude. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PlanarNikodym

theorem linearConeExtension_eq_planeIntegral {h : Plane → ℂ}
    (hh : Integrable h) (r : ℝ) (w : Plane) :
    linearConeExtension h r w = ∫ x : Plane,
      h x * planeFourierCharacter (r • w) (x.2, x.2 * x.1) := by
  have hi : Integrable (fun x : Plane =>
      h x * planeFourierCharacter (r • w) (x.2, x.2 * x.1)) :=
    hh.mul_bdd (c := 1)
      (continuous_planeFourierCharacter.comp (continuous_const.prodMk
        (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun _ => by simp)
  rw [Measure.volume_eq_prod, integral_prod_symm _ hi]
  rfl

theorem amplitudeConeExtension_eq_planeIntegral
    (b : SchwartzMap (Plane × Plane) ℂ) {h : Plane → ℂ}
    (hh : Integrable h) (r : ℝ) (w : Plane) :
    amplitudeConeExtension (fun w x => b (w, x)) h r w = ∫ x : Plane,
      b (w, x) * h x * planeFourierCharacter (r • w) (x.2, x.2 * x.1) := by
  have hi : Integrable (fun x : Plane =>
      b (w, x) * h x * planeFourierCharacter (r • w) (x.2, x.2 * x.1)) :=
    (hh.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 b)
      (b.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun x => b.norm_le_seminorm ℝ (w, x))).mul_bdd (c := 1)
      (continuous_planeFourierCharacter.comp (continuous_const.prodMk
        (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun _ => by simp)
  rw [Measure.volume_eq_prod, integral_prod_symm _ hi]
  rfl

/-- Joint continuity in the modulation and output variables follows by
absolute domination by the original L¹ data. -/
theorem continuous_modulated_linearConeExtension {h : Plane → ℂ}
    (hh : Integrable h) (r : ℝ) :
    Continuous (fun p : Plane × Plane =>
      linearConeExtension (fun x => planeFourierCharacter x p.1 * h x) r p.2) := by
  have hm (q : Plane) : Integrable (fun x : Plane => planeFourierCharacter x q * h x) :=
    hh.bdd_mul (c := 1)
      (continuous_planeFourierCharacter.comp
        (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (ae_of_all _ fun _ => by simp)
  have he : (fun p : Plane × Plane =>
      linearConeExtension (fun x => planeFourierCharacter x p.1 * h x) r p.2) =
      (fun p : Plane × Plane => ∫ x : Plane, planeFourierCharacter x p.1 * h x *
        planeFourierCharacter (r • p.2) (x.2, x.2 * x.1)) := by
    funext p
    exact linearConeExtension_eq_planeIntegral (hm p.1) r p.2
  rw [he]
  apply continuous_of_dominated (bound := fun x => ‖h x‖)
  · intro p
    exact ((hm p.1).mul_bdd (c := 1)
      (continuous_planeFourierCharacter.comp (continuous_const.prodMk
        (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun _ => by simp)).aestronglyMeasurable
  · intro p
    filter_upwards [] with x
    simp
  · exact hh.norm
  · filter_upwards [] with x
    exact ((continuous_planeFourierCharacter.comp
      (continuous_const.prodMk continuous_fst)).mul continuous_const).mul
      (continuous_planeFourierCharacter.comp
        ((continuous_const.smul continuous_snd).prodMk continuous_const))

theorem amplitudeConeIntegral_eq_fourier_superposition
    (b : SchwartzMap (Plane × Plane) ℂ) {h : Plane → ℂ}
    (hh : Integrable h) (r : ℝ) (w v : Plane) :
    (∫ x : Plane, b (w, x) * h x *
      planeFourierCharacter (r • v) (x.2, x.2 * x.1)) =
      ∫ ζ : AmplitudeFourierSpace, jointAmplitudeFourier b ζ *
        planeFourierCharacter w (amplitudeFourierEquiv ζ).1 *
        linearConeExtension
          (fun x => planeFourierCharacter x (amplitudeFourierEquiv ζ).2 * h x) r v := by
  let A := jointAmplitudeFourier b
  let F : AmplitudeFourierSpace × Plane → ℂ := fun p =>
    A p.1 * planeFourierCharacter w (amplitudeFourierEquiv p.1).1 *
      planeFourierCharacter p.2 (amplitudeFourierEquiv p.1).2 * h p.2 *
      planeFourierCharacter (r • v) (p.2.2, p.2.2 * p.2.1)
  have hF : Integrable F (volume.prod volume) := by
    apply (A.integrable.norm.mul_prod hh.norm).mono'
    · exact (((A.continuous.comp continuous_fst).mul
        (continuous_planeFourierCharacter.comp
          (continuous_const.prodMk (continuous_fst.comp
            (amplitudeFourierEquiv.continuous.comp continuous_fst))))).mul
        (continuous_planeFourierCharacter.comp
          (continuous_snd.prodMk (continuous_snd.comp
            (amplitudeFourierEquiv.continuous.comp continuous_fst))))).aestronglyMeasurable.mul
        hh.aestronglyMeasurable.comp_snd |>.mul
        (continuous_planeFourierCharacter.comp (continuous_const.prodMk
          (by fun_prop))).aestronglyMeasurable
    · filter_upwards [] with p
      simp [F]
  calc
    _ = ∫ x : Plane, ∫ ζ : AmplitudeFourierSpace, F (ζ, x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [jointAmplitudeFourier_reconstruction b w x]
      rw [← integral_mul_const, ← integral_mul_const]
    _ = ∫ ζ : AmplitudeFourierSpace, ∫ x : Plane, F (ζ, x) :=
      (integral_integral_swap hF).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ζ
      have hmod : Integrable (fun x : Plane =>
          planeFourierCharacter x (amplitudeFourierEquiv ζ).2 * h x) :=
        hh.bdd_mul (c := 1)
          (continuous_planeFourierCharacter.comp
            (continuous_id.prodMk continuous_const)).aestronglyMeasurable
          (ae_of_all _ fun _ => by simp)
      rw [linearConeExtension_eq_planeIntegral hmod, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [F, A]
      ring

theorem amplitudeConeExtension_eq_fourier_superposition
    (b : SchwartzMap (Plane × Plane) ℂ) {h : Plane → ℂ}
    (hh : Integrable h) (r : ℝ) (w : Plane) :
    amplitudeConeExtension (fun w x => b (w, x)) h r w =
      ∫ ζ : AmplitudeFourierSpace, jointAmplitudeFourier b ζ *
        planeFourierCharacter w (amplitudeFourierEquiv ζ).1 *
        linearConeExtension
          (fun x => planeFourierCharacter x (amplitudeFourierEquiv ζ).2 * h x) r w := by
  rw [amplitudeConeExtension_eq_planeIntegral b hh]
  exact amplitudeConeIntegral_eq_fourier_superposition b hh r w w

end PlanarNikodym
