import PlanarNikodym.Analysis.Fourier.GlyzPowerAverageMass

/-! Tonelli and translation identities for positive convolution along
an actual linear subspace. Extended integrals avoid artificial
integrability assumptions in the lower-degree decoupling argument. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

def glyzSubspaceAverage (μ : Measure H) (S : H →L[ℝ] E)
    (F : E → ℝ≥0∞) (x : E) : ℝ≥0∞ := ∫⁻ y, F (x - S y) ∂μ

omit [FiniteDimensional ℝ E] in
theorem measurable_glyzSubspaceAverage (μ : Measure H) [SFinite μ]
    (S : H →L[ℝ] E) {F : E → ℝ≥0∞} (hF : Measurable F) :
    Measurable (glyzSubspaceAverage μ S F) :=
  Measurable.lintegral_prod_right
    (hF.comp (continuous_fst.sub (S.continuous.comp continuous_snd)).measurable)

theorem glyzSubspaceAverage_mass (μ : Measure H) [SFinite μ]
    (S : H →L[ℝ] E) {F : E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, glyzSubspaceAverage μ S F x) = μ Set.univ * ∫⁻ x, F x := by
  unfold glyzSubspaceAverage
  have hf : Measurable (fun z : E × H => F (z.1 - S z.2)) :=
    hF.comp (continuous_fst.sub (S.continuous.comp continuous_snd)).measurable
  rw [lintegral_lintegral_swap hf.aemeasurable]
  simp_rw [lintegral_sub_right_eq_self F]
  rw [lintegral_const, mul_comm]

omit [FiniteDimensional ℝ H] in
theorem glyzSubspaceAverage_commute (μ : Measure H) (ν : Measure E)
    [SFinite μ] [SFinite ν] (S : H →L[ℝ] E)
    {F : E → ℝ≥0∞} (hF : Measurable F) (x : E) :
    glyzSubspaceAverage μ S (glyzSubspaceAverage ν (ContinuousLinearMap.id ℝ E) F) x =
      glyzSubspaceAverage ν (ContinuousLinearMap.id ℝ E) (glyzSubspaceAverage μ S F) x := by
  unfold glyzSubspaceAverage
  simp only [ContinuousLinearMap.id_apply]
  have hf : Measurable (fun z : H × E => F (x - S z.1 - z.2)) :=
    hF.comp ((continuous_const.sub (S.continuous.comp continuous_fst)).sub
      continuous_snd).measurable
  rw [lintegral_lintegral_swap hf.aemeasurable]
  apply lintegral_congr
  intro y
  apply lintegral_congr
  intro z
  congr 1
  abel

theorem glyz_lintegral_translated_pair {F G : E → ℝ≥0∞} (v : E) :
    (∫⁻ x, F (x - v) * G x) = ∫⁻ x, F x * G (x + v) := by
  simpa only [sub_add_cancel] using
    (lintegral_sub_right_eq_self (fun x => F x * G (x + v)) v)

/-- Moving an even subspace kernel from one factor to the other. -/
theorem glyzSubspaceAverage_pairing (μ : Measure H) [SFinite μ] [Measure.IsNegInvariant μ]
    (S : H →L[ℝ] E) {F G : E → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ x, glyzSubspaceAverage μ S F x * G x) =
      ∫⁻ x, F x * glyzSubspaceAverage μ S G x := by
  unfold glyzSubspaceAverage
  have hf (x : E) : Measurable (fun y => F (x - S y)) :=
    hF.comp (continuous_const.sub S.continuous).measurable
  simp_rw [← lintegral_mul_const _ (hf _)]
  rw [lintegral_lintegral_swap ((hF.comp
    (continuous_fst.sub (S.continuous.comp continuous_snd)).measurable).mul
      (hG.comp measurable_fst)).aemeasurable]
  simp_rw [glyz_lintegral_translated_pair]
  rw [lintegral_lintegral_swap ((hF.comp measurable_snd).mul
    (hG.comp (continuous_snd.add (S.continuous.comp continuous_fst)).measurable)).aemeasurable]
  apply lintegral_congr
  intro x
  have hg : Measurable (fun y => G (x + S y)) :=
    hG.comp (continuous_const.add S.continuous).measurable
  rw [lintegral_const_mul _ hg]
  congr 1
  simpa only [map_neg, sub_neg_eq_add] using
    (lintegral_neg_eq_self (μ := μ) (fun y => G (x - S y)))

/-- Absorbing the averaged weight after transferring the subspace kernel. -/
theorem glyzSubspaceAverage_pairing_le (μ : Measure H) [SFinite μ] [Measure.IsNegInvariant μ]
    (S : H →L[ℝ] E) {F G : E → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (hGavg : ∀ x, glyzSubspaceAverage μ S G x ≤ C * G x) :
    (∫⁻ x, glyzSubspaceAverage μ S F x * G x) ≤ C * ∫⁻ x, F x * G x := by
  rw [glyzSubspaceAverage_pairing μ S hF hG]
  calc
    _ ≤ ∫⁻ x, C * (F x * G x) := lintegral_mono fun x =>
      (mul_le_mul' le_rfl (hGavg x)).trans_eq (by ring)
    _ = _ := lintegral_const_mul' _ _ hC

end PlanarNikodym
