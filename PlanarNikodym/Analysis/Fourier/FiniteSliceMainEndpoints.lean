import PlanarNikodym.Analysis.Fourier.PartialExtensionLinearity
import PlanarNikodym.Analysis.Fourier.PartialExtensionMeasurability
import PlanarNikodym.Analysis.Fourier.FiniteCinematicMainL2
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! The original finite family of main pieces as one operator on the
product of counting measure and the selected-parameter plane. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace PlanarNikodym

def finiteSliceMainMeasure (N : ℕ) : Measure (Fin N × Aux 2) :=
  Measure.count.prod volume

instance finiteSliceMainMeasure_sfinite (N : ℕ) : SFinite (finiteSliceMainMeasure N) := by
  unfold finiteSliceMainMeasure
  infer_instance

def Family.finiteSliceMain {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (r b δ : ℝ) (N : ℕ)
    (q : Aux 2 → Parameters 2 d) (f : Plane → ℂ) (w : Fin N × Aux 2) : ℂ :=
  G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ b δ w.1.val) L β r f (q w.2)

theorem Family.measurable_finiteSliceMain {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (ha : ∀ x ∈ tsupport χ, AnalyticAt ℝ (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    (r b δ : ℝ) (N : ℕ) (q : Aux 2 → Parameters 2 d) (hq : Measurable q)
    {f : Plane → ℂ} (hf : Integrable f) :
    Measurable (G.finiteSliceMain χ L β r b δ N q f) := by
  apply measurable_from_prod_countable_right
  intro j
  have hj : Continuous (scaleTimeLocalizedCutoff χ b δ j.val) :=
    hχ.mul ((contDiff_scaleTimeCutoff b δ j.val).continuous.comp continuous_fst)
  exact (G.stronglyMeasurable_cutoffPartialExtension _ hj
    (hasCompactSupport_scaleTimeLocalizedCutoff hc b δ j.val)
    (fun x hx => ha x (tsupport_scaleTimeLocalizedCutoff_subset χ b δ j.val hx))
    L hβ hf r).measurable.comp hq

theorem Family.finiteSliceMain_add {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    (r b δ : ℝ) (N : ℕ) (q : Aux 2 → Parameters 2 d)
    {f g : Plane → ℂ} (hf : Integrable f) (hg : Integrable g) :
    G.finiteSliceMain χ L β r b δ N q (f + g) =
      G.finiteSliceMain χ L β r b δ N q f + G.finiteSliceMain χ L β r b δ N q g := by
  funext w
  have hj : Continuous (scaleTimeLocalizedCutoff χ b δ w.1.val) :=
    hχ.mul ((contDiff_scaleTimeCutoff b δ w.1.val).continuous.comp continuous_fst)
  exact congrFun (G.cutoffPartialExtension_add _ hj
    (hasCompactSupport_scaleTimeLocalizedCutoff hc b δ w.1.val)
    (fun x hx => hγ x (tsupport_scaleTimeLocalizedCutoff_subset χ b δ w.1.val hx))
    L β hβ hf hg r) (q w.2)

theorem Family.lintegral_finiteSliceMain {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (ha : ∀ x ∈ tsupport χ, AnalyticAt ℝ (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    (r b δ : ℝ) (N : ℕ) (q : Aux 2 → Parameters 2 d) (hq : Measurable q)
    {f : Plane → ℂ} (hf : Integrable f) (p : ℝ) :
    (∫⁻ w, ‖G.finiteSliceMain χ L β r b δ N q f w‖ₑ ^ p ∂finiteSliceMainMeasure N) =
      ∑ j ∈ Finset.range N, ∫⁻ z : Aux 2,
        ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ b δ j) L β r f (q z)‖ₑ ^ p := by
  have hm := (G.measurable_finiteSliceMain χ hχ hc ha L β hβ r b δ N q hq hf).enorm.pow_const p
  rw [finiteSliceMainMeasure, lintegral_prod _ hm.aemeasurable, lintegral_count, tsum_fintype]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => ∫⁻ z : Aux 2,
    ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ b δ j) L β r f (q z)‖ₑ ^ p) N

/-- The same pointwise L∞ constant works on every selected plane and
for every finite number of time pieces. Counting the pieces introduces
no loss in the L∞ endpoint. -/
theorem Family.exists_uniform_finiteSliceMain_LInfinity {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ b δ : ℝ, 0 < δ → ∀ N : ℕ,
      ∀ q : Aux 2 → Parameters 2 d, ∀ f : Plane → ℂ, Integrable f →
      ∀ w : Fin N × Aux 2, ‖G.finiteSliceMain χ L β r b δ N q f w‖ₑ ≤
        ENNReal.ofReal (C * δ) * eLpNorm f ∞ volume := by
  obtain ⟨C, hC, h⟩ := G.exists_uniform_cutoffPartialExtension_time_piece_LInfinity
    χ hχ hc hγ L β hβ
  refine ⟨C + 1, by linarith, fun r hr b δ hδ N q f hf w => ?_⟩
  apply ((h r hr b δ hδ w.1.val f hf).1 (q w.2)).trans
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by nlinarith : C * δ ≤ (C + 1) * δ)) _

end PlanarNikodym
