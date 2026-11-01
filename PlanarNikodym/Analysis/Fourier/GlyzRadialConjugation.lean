import PlanarNikodym.Analysis.Fourier.GlyzTimeTranslation

/-! The negative radial-frequency component is the complex conjugate of
an actual positive-frequency extension for the same cinematic phase. -/
noncomputable section
open Set MeasureTheory Complex
open scoped ContDiff ENNReal ComplexConjugate
namespace PlanarNikodym
set_option backward.isDefEq.respectTransparency false

def glyzRadialConjugateInput (g : Plane → ℂ) : Plane → ℂ :=
  fun y => conj (g (y.1, -y.2))

def glyzRadialConjugateAmplitude {P : Type*} (a : P × Plane → ℂ) : P × Plane → ℂ :=
  fun x => conj (a (x.1, x.2.1, -x.2.2))

theorem measurePreserving_radialReflection :
    MeasurePreserving (fun y : Plane => (y.1, -y.2)) volume volume := by
  change MeasurePreserving (Prod.map (id : ℝ → ℝ) Neg.neg)
    ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume)
  exact (MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_neg (volume : Measure ℝ))

theorem integrable_glyzRadialConjugateInput {g : Plane → ℂ} (hg : Integrable g) :
    Integrable (glyzRadialConjugateInput g) := by
  have h : Integrable (fun y : Plane => g (y.1, -y.2)) :=
    memLp_one_iff_integrable.mp
      ((memLp_one_iff_integrable.mpr hg).comp_measurePreserving measurePreserving_radialReflection)
  exact Complex.conjCLE.toContinuousLinearMap.integrable_comp h

theorem lintegral_enorm_glyzRadialConjugateInput (g : Plane → ℂ) :
    (∫⁻ y, ‖glyzRadialConjugateInput g y‖ₑ) = ∫⁻ y, ‖g y‖ₑ := by
  have he (y : Plane) : ‖glyzRadialConjugateInput g y‖ₑ = ‖g (y.1, -y.2)‖ₑ := by
    rw [← ofReal_norm, glyzRadialConjugateInput, norm_conj, ofReal_norm]
  simp_rw [he]
  exact measurePreserving_radialReflection.lintegral_comp_emb
    (Homeomorph.prodCongr (Homeomorph.refl ℝ) (Homeomorph.neg ℝ)).measurableEmbedding
      (fun y : Plane => ‖g y‖ₑ)

theorem contDiff_glyzRadialConjugateAmplitude {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {a : P × Plane → ℂ}
    (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (glyzRadialConjugateAmplitude a) :=
  Complex.conjCLE.contDiff.comp
    (ha.comp (contDiff_fst.prodMk (contDiff_snd.fst.prodMk contDiff_snd.snd.neg)))

theorem hasCompactSupport_glyzRadialConjugateAmplitude {P : Type*}
    [TopologicalSpace P] {a : P × Plane → ℂ} (hc : HasCompactSupport a) :
    HasCompactSupport (glyzRadialConjugateAmplitude a) := by
  let e := Homeomorph.prodCongr (Homeomorph.refl P)
    (Homeomorph.prodCongr (Homeomorph.refl ℝ) (Homeomorph.neg ℝ))
  exact (hc.comp_homeomorph e).comp_left (g := fun z : ℂ => conj z) (by simp)

theorem phaseOscillation_radial_conjugate (φ : ℝ → ℝ) (r η t : ℝ) :
    phaseOscillation φ (r * η) t = conj (phaseOscillation φ (r * -η) t) := by
  unfold phaseOscillation
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  push_cast
  ring

theorem glyzRawExtension_radial_conjugate {P : Type}
    (Φ : P × ℝ → ℝ) (a : P × Plane → ℂ) (g : Plane → ℂ) (r : ℝ) :
    glyzRawExtension Φ (glyzRadialConjugateAmplitude a) (glyzRadialConjugateInput g) r =
      fun p => conj (glyzRawExtension Φ a g r p) := by
  funext p
  unfold glyzRawExtension
  rw [← integral_conj]
  have hinner (η : ℝ) :
      (∫ t, phaseOscillation (fun s => Φ (p, s)) (r * η) t *
        glyzRadialConjugateAmplitude a (p, t, η) * glyzRadialConjugateInput g (t, η)) =
      conj (∫ t, phaseOscillation (fun s => Φ (p, s)) (r * -η) t *
        a (p, t, -η) * g (t, -η)) := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [phaseOscillation_radial_conjugate _ r η t]
    simp only [glyzRadialConjugateAmplitude, glyzRadialConjugateInput, map_mul]
  simp_rw [hinner]
  exact integral_neg_eq_self (fun η : ℝ => conj (∫ t, phaseOscillation (fun s => Φ (p, s)) (r * η) t * a (p, t, η) * g (t, η))) (volume : Measure ℝ)

theorem timeSliceExtension_radial_conjugate {P : Type}
    (Φ : P × ℝ → ℝ) (a : P × Plane → ℂ) (g : Plane → ℂ) (r c δ : ℝ) :
    timeSliceExtension Φ (glyzRadialConjugateAmplitude a) (glyzRadialConjugateInput g) r c δ =
      fun p => conj (timeSliceExtension Φ a g r c δ p) := by
  let b : P × Plane → ℂ := fun z => a z * (timePartitionWindow ((z.2.1 - c) / δ) : ℂ)
  have he : timeSliceExtension Φ a g r c δ = glyzRawExtension Φ b g r := by
    funext p
    unfold timeSliceExtension glyzRawExtension
    congr 1
    funext η
    congr 1
    funext t
    dsimp only [b]
    ring
  rw [he, ← glyzRawExtension_radial_conjugate]
  funext p
  unfold timeSliceExtension glyzRawExtension
  congr 1
  funext η
  congr 1
  funext t
  simp only [b, glyzRadialConjugateAmplitude, map_mul, Complex.conj_ofReal]
  ring

end PlanarNikodym
