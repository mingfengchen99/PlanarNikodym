import PlanarNikodym.Analysis.Fourier.GlyzSchwartzTranslation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Continuous-center globalization of genuine local integral bounds.
Tonelli's theorem counts each supported point by exactly one ball mass;
the translated weight contributes only its total mass. -/
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal BigOperators
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

/-- Integrating local ball integrals over all centers which can see the
support gives exactly the ball volume times the full integral. -/
theorem glyz_lintegral_centers_closedBall (F : E → ℝ≥0∞) (hF : Measurable F)
    (L ρ : ℝ) (hs : Function.support F ⊆ closedBall (0 : E) L) :
    (∫⁻ a in closedBall (0 : E) (L + ρ), ∫⁻ x in closedBall a ρ, F x ∂μ ∂μ) =
      μ (closedBall (0 : E) ρ) * ∫⁻ x, F x ∂μ := by
  let B := closedBall (0 : E) (L + ρ)
  let K : E → E → ℝ≥0∞ := fun a x => (closedBall a ρ).indicator F x
  have hK : Measurable (Function.uncurry K) := by
    change Measurable (fun z : E × E => (closedBall z.1 ρ).indicator F z.2)
    have he : (fun z : E × E => (closedBall z.1 ρ).indicator F z.2) =
        {z : E × E | dist z.2 z.1 ≤ ρ}.indicator (fun z => F z.2) := by
      funext z
      simp only [Set.indicator, mem_closedBall, mem_setOf_eq]
    rw [he]
    exact (hF.comp measurable_snd).indicator (measurableSet_le (by fun_prop) measurable_const)
  have hcenter (x : E) : (∫⁻ a in B, K a x ∂μ) = F x * μ (closedBall (0 : E) ρ) := by
    have he (a : E) : K a x = (closedBall x ρ).indicator (fun _ => F x) a := by
      simp only [K, Set.indicator, mem_closedBall, dist_comm]
    simp_rw [he]
    by_cases hx : F x = 0
    · simp [hx]
    · have hxL : dist x 0 ≤ L := hs hx
      have hsub : closedBall x ρ ⊆ B := by
        intro a ha
        have hax : dist a x ≤ ρ := ha
        exact (dist_triangle a x 0).trans (by linarith)
      rw [lintegral_indicator measurableSet_closedBall, lintegral_const,
        Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_closedBall,
        inter_eq_left.mpr hsub, addHaar_closedBall_center μ x ρ]
  calc
    _ = ∫⁻ a in B, ∫⁻ x, K a x ∂μ ∂μ := by
      apply lintegral_congr
      intro a
      exact (lintegral_indicator measurableSet_closedBall F).symm
    _ = ∫⁻ x, ∫⁻ a in B, K a x ∂μ ∂μ := lintegral_lintegral_swap hK.aemeasurable
    _ = ∫⁻ x, F x * μ (closedBall (0 : E) ρ) ∂μ := lintegral_congr hcenter
    _ = _ := by rw [lintegral_mul_const _ hF, mul_comm]

/-- The exact total mass of a translated weighted integral. -/
theorem glyz_lintegral_centers_weight (F W : E → ℝ≥0∞)
    (hF : Measurable F) (hW : Measurable W) :
    (∫⁻ a, ∫⁻ x, F x * W (x - a) ∂μ ∂μ) =
      (∫⁻ x, W x ∂μ) * ∫⁻ x, F x ∂μ := by
  have hi (x : E) : (∫⁻ a, F x * W (x - a) ∂μ) = F x * ∫⁻ a, W a ∂μ := by
    have hwx : Measurable (fun a : E => W (x - a)) :=
      hW.comp (measurable_const.sub measurable_id)
    rw [lintegral_const_mul (F x) hwx, lintegral_sub_left_eq_self W]
  calc
    _ = ∫⁻ x, ∫⁻ a, F x * W (x - a) ∂μ ∂μ :=
      lintegral_lintegral_swap ((hF.comp measurable_snd).mul
        (hW.comp (measurable_snd.sub measurable_fst))).aemeasurable
    _ = ∫⁻ x, F x * (∫⁻ a, W a ∂μ) ∂μ := lintegral_congr hi
    _ = _ := by rw [lintegral_mul_const _ hF, mul_comm]

/-- The error is paid once per center, with the exact volume ratio.
Only the function on the left needs compact spatial support; the pieces
on the right can be arbitrary measurable functions. -/
theorem glyz_continuous_center_globalization {ι : Type*} (I : Finset ι)
    (F : E → ℝ≥0∞) (G : ι → E → ℝ≥0∞) (W : E → ℝ≥0∞)
    (hF : Measurable F) (hG : ∀ i ∈ I, Measurable (G i)) (hW : Measurable W)
    (L : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hs : Function.support F ⊆ closedBall (0 : E) L) (D e : ℝ≥0∞)
    (hlocal : ∀ a ∈ closedBall (0 : E) (L + ρ),
      (∫⁻ x in closedBall a ρ, F x ∂μ) ≤
        D * ∑ i ∈ I, (∫⁻ x, G i x * W (x - a) ∂μ) + e) :
    (∫⁻ x, F x ∂μ) ≤
      D * ((∫⁻ x, W x ∂μ) / μ (closedBall (0 : E) ρ)) *
        ∑ i ∈ I, (∫⁻ x, G i x ∂μ) +
      e * (μ (closedBall (0 : E) (L + ρ)) / μ (closedBall (0 : E) ρ)) := by
  let B := closedBall (0 : E) (L + ρ)
  let H : E → ℝ≥0∞ := fun a => ∑ i ∈ I, (∫⁻ x, G i x * W (x - a) ∂μ)
  have hH : Measurable H := by
    apply Finset.measurable_sum I
    intro i hi
    exact ((hG i hi |>.comp measurable_snd).mul
      (hW.comp (measurable_snd.sub measurable_fst))).lintegral_prod_right
  have hall : (∫⁻ a, H a ∂μ) =
      (∫⁻ x, W x ∂μ) * ∑ i ∈ I, (∫⁻ x, G i x ∂μ) := by
    rw [lintegral_finsetSum I]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact glyz_lintegral_centers_weight μ (G i) W (hG i hi) hW
    · intro i hi
      exact ((hG i hi |>.comp measurable_snd).mul
        (hW.comp (measurable_snd.sub measurable_fst))).lintegral_prod_right
  have hbound : μ (closedBall (0 : E) ρ) * (∫⁻ x, F x ∂μ) ≤
      D * ((∫⁻ x, W x ∂μ) * ∑ i ∈ I, (∫⁻ x, G i x ∂μ)) + e * μ B := by
    rw [← glyz_lintegral_centers_closedBall μ F hF L ρ hs]
    calc
      _ ≤ ∫⁻ a in B, D * H a + e ∂μ := setLIntegral_mono' measurableSet_closedBall hlocal
      _ = D * (∫⁻ a in B, H a ∂μ) + e * μ B := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hH, lintegral_const, Measure.restrict_apply_univ]
      _ ≤ D * (∫⁻ a, H a ∂μ) + e * μ B := by
        gcongr
        exact Measure.restrict_le_self
      _ = _ := by rw [hall]
  have hmass0 : μ (closedBall (0 : E) ρ) ≠ 0 := (measure_closedBall_pos μ 0 hρ).ne'
  have hmassT : μ (closedBall (0 : E) ρ) ≠ ⊤ := measure_closedBall_lt_top.ne
  calc
    _ = (μ (closedBall (0 : E) ρ))⁻¹ *
        (μ (closedBall (0 : E) ρ) * ∫⁻ x, F x ∂μ) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hmass0 hmassT, one_mul]
    _ ≤ (μ (closedBall (0 : E) ρ))⁻¹ *
        (D * ((∫⁻ x, W x ∂μ) * ∑ i ∈ I, (∫⁻ x, G i x ∂μ)) + e * μ B) := by
      gcongr
    _ = _ := by
      simp only [ENNReal.div_eq_inv_mul, mul_add, B]
      ac_rfl

end PlanarNikodym
