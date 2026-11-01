import PlanarNikodym.Analysis.Fourier.FourierReconstruction
import PlanarNikodym.Analysis.Maximal.LowFrequencyEstimate
import PlanarNikodym.Analysis.Maximal.PositiveCutoffComparison

/-! Assemble actual Fourier reconstruction and the proved low-frequency
estimate. Only the high-frequency analytic estimate remains an input. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym
namespace Family
variable {d : ℕ} (G : Family 2 d)

theorem cutoffMaximal_reconstruction_majorant (χ : Cutoff d) (L : FrequencyCutoff)
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : Continuous f) (hfi : Integrable f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (z : Base 2) :
    G.cutoffMaximal χ f z ≤ G.cutoffMaximal χ (L.low f) z +
      ∑' k, G.cutoffMaximal χ (L.band k f) z := by
  apply iSup_le
  intro u
  exact (G.cutoffAverage_reconstruction_majorant χ L hχ hc hγ hf hfi hB (z, u)).trans
    (add_le_add (le_iSup_of_le u le_rfl)
      (ENNReal.tsum_le_tsum (fun k => le_iSup_of_le u le_rfl)))

/-- A summably decaying dyadic maximal estimate implies the open-set
estimate, with all low-frequency, reconstruction and measurability steps
proved from the actual operators. -/
theorem openMaximalEstimate_of_dyadic_decay (U : Set (Parameters 2 d))
    (hopen : IsOpen U) (hU : U ⊆ G.W) (hs : G.IsSmooth)
    (χ : Cutoff d) (L : FrequencyCutoff) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ t ∈ G.I.carrier, ∀ p ∈ U, 1 ≤ χ (t, p))
    (p : ℝ≥0) (hp : 1 ≤ p) (ε : ℝ) (hε : ε < 1 / (p : ℝ))
    (hH : DyadicMaximalEstimate G χ L p ε) : G.OpenMaximalEstimate U := by
  obtain ⟨CL, hCL⟩ := lowFrequencyInput_of_compactCutoff G χ L p hχ hc hp
  obtain ⟨CH, hCH⟩ := hH
  let a : ℝ := -1 / (p : ℝ) + ε
  have ha : a < 0 := by dsimp [a]; rw [neg_div]; linarith
  let C : ℝ≥0∞ := CL + (CH : ℝ≥0∞) * ∑' k, dyadicWeight a k
  have hC : C ≠ ⊤ := by
    exact (ENNReal.add_lt_top.mpr ⟨ENNReal.coe_lt_top,
      ENNReal.mul_lt_top ENNReal.coe_lt_top (dyadicWeight_tsum_lt_top ha)⟩).ne
  apply G.openMaximalEstimate_of_smooth_tests U hU hs p hp C.toNNReal
  intro f hf h0 h1 hi hlp
  refine ⟨G.measurable_positiveMaximal U hopen hU hs hf.continuous h0 h1, ?_⟩
  let fC : Plane → ℂ := fun x => (f x : ℂ)
  have hfc : Continuous fC := Complex.continuous_ofReal.comp hf.continuous
  have hfb (x : Plane) : ‖fC x‖ ≤ 1 := by
    simpa only [fC, Complex.norm_real, Real.norm_of_nonneg (h0 x)] using h1 x
  have hmL : Measurable (G.cutoffMaximal χ (L.low fC)) :=
    G.measurable_cutoffMaximal (G.continuous_cutoffAverage hχ hc hγ (L.low_continuous hi))
  have hmH (k : ℕ) : Measurable (G.cutoffMaximal χ (L.band k fC)) :=
    G.measurable_cutoffMaximal (G.continuous_cutoffAverage hχ hc hγ (L.band_continuous k hi))
  have hrec (z : Base 2) : G.positiveMaximal U (fun x => ENNReal.ofReal (f x)) z ≤
      G.cutoffMaximal χ (L.low fC) z + ∑' k, G.cutoffMaximal χ (L.band k fC) z :=
    (G.positiveMaximal_le_cutoffMaximal U hχ hc hγ hχ0 hχ1 hf.continuous h0 z).trans
      (G.cutoffMaximal_reconstruction_majorant χ L hχ hc hγ hfc hi hfb z)
  have hsum := dyadic_majorant_estimate volume p hp
    (fun z => ∑' k, G.cutoffMaximal χ (L.band k fC) z)
    (fun k => G.cutoffMaximal χ (L.band k fC)) hmH (fun _ => le_rfl)
    a CH (eLpNorm fC p volume) (fun k => hCH k fC hi hlp)
  calc
    _ ≤ eLpNorm (fun z => G.cutoffMaximal χ (L.low fC) z +
        ∑' k, G.cutoffMaximal χ (L.band k fC) z) p volume :=
      eLpNorm_mono_enorm (by simpa only [enorm_eq_self] using hrec)
    _ ≤ eLpNorm (G.cutoffMaximal χ (L.low fC)) p volume +
        eLpNorm (fun z => ∑' k, G.cutoffMaximal χ (L.band k fC) z) p volume :=
      eLpNorm_add_le hmL.stronglyMeasurable.aestronglyMeasurable
        (Measurable.tsum hmH).stronglyMeasurable.aestronglyMeasurable
        (by exact_mod_cast hp)
    _ ≤ (CL : ℝ≥0∞) * eLpNorm fC p volume +
        ((CH : ℝ≥0∞) * ∑' k, dyadicWeight a k) * eLpNorm fC p volume :=
      add_le_add (hCL fC hi hlp) hsum
    _ = _ := by rw [← add_mul, ENNReal.coe_toNNReal hC]

theorem openMaximalEstimate_of_jet_inputs (U : Set (Parameters 2 d))
    (hopen : IsOpen U) (hU : U ⊆ G.W) (hs : G.IsSmooth)
    (χ : Cutoff d) (L : FrequencyCutoff) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ t ∈ G.I.carrier, ∀ p ∈ U, 1 ≤ χ (t, p))
    (p : ℝ≥0) (hp : 1 ≤ p) (s : ℕ) (ε δ : ℝ) (hloss : ε + δ < 1 / (p : ℝ))
    (hS : JetSmoothingInput G χ L p s ε) (hB : BandSobolevInput G χ L p s δ) :
    G.OpenMaximalEstimate U :=
  G.openMaximalEstimate_of_dyadic_decay U hopen hU hs χ L hχ hc hγ hχ0 hχ1 p hp
    (ε + δ) hloss (corollary_2_2_of_inputs G χ L p s ε δ hS hB)

end Family

/-- Local data for the smooth-test route. Low-frequency control and Fourier
reconstruction are proved; only smoothing and the general-dimensional
Sobolev estimate remain analytic proof fields. -/
structure SmoothMaximalPackage {d : ℕ} (G : Family 2 d)
    (U : Set (Parameters 2 d)) where
  frequency : FrequencyCutoff
  cutoff : Cutoff d
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_compact : HasCompactSupport cutoff
  gamma_regular_at_support : ∀ x ∈ tsupport cutoff,
    ContDiffAt ℝ 1 (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x
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

theorem SmoothMaximalPackage.open_maximal_estimate {d : ℕ} {G : Family 2 d}
    {U : Set (Parameters 2 d)} (D : SmoothMaximalPackage G U)
    (hopen : IsOpen U) (hU : U ⊆ G.W) (hs : G.IsSmooth) : G.OpenMaximalEstimate U :=
  G.openMaximalEstimate_of_jet_inputs U hopen hU hs D.cutoff D.frequency
    D.cutoff_smooth.continuous D.cutoff_compact
    (fun x hx => (D.gamma_regular_at_support x hx).continuousAt)
    D.cutoff_nonnegative D.cutoff_one D.p D.p_ge_one D.jetOrder
    D.smoothingLoss D.sobolevLoss D.loss_lt D.smoothing D.sobolev

end PlanarNikodym
