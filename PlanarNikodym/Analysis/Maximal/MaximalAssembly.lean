import PlanarNikodym.Analysis.Maximal.LocalSmoothing
import PlanarNikodym.Analysis.Maximal.MaximalExclusion
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym

/-- Proved for continuous compactly supported cutoffs and `p ≥ 1` by
`lowFrequencyInput_of_compactCutoff` in `LowFrequencyEstimate`. -/
def LowFrequencyInput {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (L : FrequencyCutoff) (p : ℝ≥0) : Prop :=
  ∃ C : ℝ≥0, ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
    eLpNorm (G.cutoffMaximal χ (L.low f)) p volume ≤ C * eLpNorm f p volume

/-- Pointwise Fourier reconstruction/approximation on curves, including
measurability. This is an explicit remaining obligation: ambient `Lp`
convergence alone does not imply convergence on individual curves.
No norm estimate or incidence-null conclusion is assumed here. -/
def OpenReconstructionInput {d : ℕ} (G : Family 2 d)
    (U : Set (Parameters 2 d)) (χ : Cutoff d) (L : FrequencyCutoff) : Prop :=
  ∀ O : Set Plane, IsOpen O → volume O < ⊤ →
    Measurable (G.positiveMaximal U (O.indicator (fun _ => 1))) ∧
    Measurable (G.cutoffMaximal χ (L.low (O.indicator (fun _ => 1)))) ∧
    (∀ k, Measurable (G.cutoffMaximal χ (L.band k (O.indicator (fun _ => 1))))) ∧
    ∀ z, G.positiveMaximal U (O.indicator (fun _ => 1)) z ≤
      G.cutoffMaximal χ (L.low (O.indicator (fun _ => 1))) z +
        ∑' k, G.cutoffMaximal χ (L.band k (O.indicator (fun _ => 1))) z

/-- Explicit data and still-unproved analytic inputs for a localized
compact interval. All operators in these inputs are the actual integrals
defined in `Averaging` and `FrequencyLocalization`. -/
structure AnalyticMaximalPackage {d : ℕ} (G : Family 2 d)
    (U : Set (Parameters 2 d)) where
  frequency : FrequencyCutoff
  cutoff : Cutoff d
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_compact : HasCompactSupport cutoff
  gamma_smooth_near_cutoff : ContDiffOn ℝ ∞ (fun x => G.γ x.1 x.2) (tsupport cutoff)
  cutoff_nonnegative : ∀ x, 0 ≤ cutoff x
  cutoff_one : ∀ t ∈ G.I.carrier, ∀ q ∈ U, 1 ≤ cutoff (t, q)
  p : ℝ≥0
  p_ge_one : 1 ≤ p
  p_ge_threshold : smoothingThreshold d ≤ p
  jetOrder : ℕ
  jetOrder_gt : (d : ℝ) / (p : ℝ) < jetOrder
  smoothingLoss : ℝ
  sobolevLoss : ℝ
  smoothingLoss_pos : 0 < smoothingLoss
  sobolevLoss_pos : 0 < sobolevLoss
  loss_lt : smoothingLoss + sobolevLoss < 1 / (p : ℝ)
  smoothing : JetSmoothingInput G cutoff frequency p jetOrder smoothingLoss
  sobolev : BandSobolevInput G cutoff frequency p jetOrder sobolevLoss
  low : LowFrequencyInput G cutoff frequency p
  reconstruction : OpenReconstructionInput G U cutoff frequency

theorem AnalyticMaximalPackage.high_frequency_decay {d : ℕ} {G : Family 2 d}
    {U : Set (Parameters 2 d)} (D : AnalyticMaximalPackage G U) :
    DyadicMaximalEstimate G D.cutoff D.frequency D.p (D.smoothingLoss + D.sobolevLoss) :=
  corollary_2_2_of_inputs G D.cutoff D.frequency D.p D.jetOrder
    D.smoothingLoss D.sobolevLoss D.smoothing D.sobolev

/-- Low-frequency control + summable high-frequency decay + pointwise
reconstruction prove the open-test maximal estimate. -/
theorem AnalyticMaximalPackage.open_maximal_estimate {d : ℕ} {G : Family 2 d}
    {U : Set (Parameters 2 d)} (D : AnalyticMaximalPackage G U) :
    G.OpenMaximalEstimate U := by
  classical
  obtain ⟨CL, hCL⟩ := D.low
  obtain ⟨CH, hCH⟩ := D.high_frequency_decay
  let a : ℝ := -1 / (D.p : ℝ) + (D.smoothingLoss + D.sobolevLoss)
  have ha : a < 0 := by dsimp [a]; rw [neg_div]; linarith [D.loss_lt]
  let C : ℝ≥0∞ := CL + (CH : ℝ≥0∞) * ∑' k, dyadicWeight a k
  have hC : C ≠ ⊤ := by
    exact (ENNReal.add_lt_top.mpr ⟨ENNReal.coe_lt_top,
      ENNReal.mul_lt_top ENNReal.coe_lt_top (dyadicWeight_tsum_lt_top ha)⟩).ne
  refine ⟨D.p, D.p_ge_one, C.toNNReal, ?_⟩
  intro O hO hOf
  obtain ⟨hm, hmL, hmH, hrec⟩ := D.reconstruction O hO hOf
  refine ⟨hm, ?_⟩
  let f : Plane → ℂ := O.indicator (fun _ => 1)
  have hi : Integrable f := (integrable_indicator_iff hO.measurableSet).mpr
    (integrableOn_const hOf.ne)
  have hf : MemLp f D.p volume :=
    memLp_indicator_const D.p hO.measurableSet 1 (Or.inr hOf.ne)
  have hsum := dyadic_majorant_estimate volume D.p D.p_ge_one
    (fun z => ∑' k, G.cutoffMaximal D.cutoff (D.frequency.band k f) z)
    (fun k => G.cutoffMaximal D.cutoff (D.frequency.band k f)) hmH
    (fun _ => le_rfl) a CH (eLpNorm f D.p volume) (fun k => hCH k f hi hf)
  have hlow := hCL f hi hf
  have hp0 : D.p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one D.p_ge_one)
  have hn : eLpNorm f D.p volume = volume O ^ (1 / (D.p : ℝ)) := by
    simp [f, eLpNorm_indicator_const hO.measurableSet
      (by exact_mod_cast hp0 : (D.p : ℝ≥0∞) ≠ 0) ENNReal.coe_ne_top]
  calc
    _ ≤ eLpNorm (fun z => G.cutoffMaximal D.cutoff (D.frequency.low f) z +
        ∑' k, G.cutoffMaximal D.cutoff (D.frequency.band k f) z) D.p volume :=
      eLpNorm_mono_enorm (by simpa only [enorm_eq_self] using hrec)
    _ ≤ eLpNorm (G.cutoffMaximal D.cutoff (D.frequency.low f)) D.p volume +
        eLpNorm (fun z => ∑' k, G.cutoffMaximal D.cutoff (D.frequency.band k f) z) D.p volume := by
      exact eLpNorm_add_le hmL.stronglyMeasurable.aestronglyMeasurable
        (Measurable.tsum hmH).stronglyMeasurable.aestronglyMeasurable
        (by exact_mod_cast D.p_ge_one)
    _ ≤ (CL : ℝ≥0∞) * eLpNorm f D.p volume +
        ((CH : ℝ≥0∞) * ∑' k, dyadicWeight a k) * eLpNorm f D.p volume := add_le_add hlow hsum
    _ = _ := by rw [← add_mul, hn, ENNReal.coe_toNNReal hC]

theorem AnalyticMaximalPackage.incidence_null {d : ℕ} {G : Family 2 d}
    {U : Set (Parameters 2 d)} (D : AnalyticMaximalPackage G U)
    (hU : U ⊆ G.W) (hs : G.IsSmooth)
    (E : Set Plane) (hE : MeasurableSet E) (hE0 : volume E = 0) :
    volume (G.timeIncidenceCenters U E) = 0 :=
  D.open_maximal_estimate.incidence_null hU hs E hE hE0

end PlanarNikodym
