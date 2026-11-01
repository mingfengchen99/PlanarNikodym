import PlanarNikodym.Analysis.Maximal.E2AnalyticExponentRange
import PlanarNikodym.Analysis.Maximal.SmoothMaximalAssembly

/-! Low frequencies and actual Fourier reconstruction complete the
fixed-exponent maximal estimate on the original bounded continuous
L¹ ∩ Lᵖ tests. No extension to arbitrary Lᵖ representatives is claimed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym

theorem Family.cutoffMaximal_continuous_tests_of_summable_dyadic_e2 {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : 1 ≤ p) {η : ℝ} (hη : 0 < η)
    (CH : ℝ≥0)
    (hH : ∀ k : ℕ, ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffMaximal χ (L.band k f)) p volume ≤
        CH * dyadicWeight (-η) k * eLpNorm f p volume) :
    ∃ C : ℝ≥0, ∀ f : Plane → ℂ, Continuous f → Integrable f → MemLp f p volume →
      (∃ B : ℝ, ∀ x, ‖f x‖ ≤ B) →
      Measurable (G.cutoffMaximal χ f) ∧
        eLpNorm (G.cutoffMaximal χ f) p volume ≤ C * eLpNorm f p volume := by
  obtain ⟨CL, hCL⟩ := lowFrequencyInput_of_compactCutoff G χ L p hχ hc hp
  let C : ℝ≥0∞ := CL + (CH : ℝ≥0∞) * ∑' k, dyadicWeight (-η) k
  have hC : C ≠ ⊤ := by
    exact (ENNReal.add_lt_top.mpr ⟨ENNReal.coe_lt_top,
      ENNReal.mul_lt_top ENNReal.coe_lt_top (dyadicWeight_tsum_lt_top (neg_neg_of_pos hη))⟩).ne
  refine ⟨C.toNNReal, ?_⟩
  intro f hfc hfi hfp hfB
  obtain ⟨B, hB⟩ := hfB
  refine ⟨G.measurable_cutoffMaximal (G.continuous_cutoffAverage hχ hc hγ hfc), ?_⟩
  have hmL : Measurable (G.cutoffMaximal χ (L.low f)) :=
    G.measurable_cutoffMaximal (G.continuous_cutoffAverage hχ hc hγ (L.low_continuous hfi))
  have hmH (k : ℕ) : Measurable (G.cutoffMaximal χ (L.band k f)) :=
    G.measurable_cutoffMaximal (G.continuous_cutoffAverage hχ hc hγ (L.band_continuous k hfi))
  have hrec := G.cutoffMaximal_reconstruction_majorant χ L hχ hc hγ hfc hfi hB
  have hsum := dyadic_majorant_estimate volume p hp
    (fun z => ∑' k, G.cutoffMaximal χ (L.band k f) z)
    (fun k => G.cutoffMaximal χ (L.band k f)) hmH (fun _ => le_rfl)
    (-η) CH (eLpNorm f p volume) (fun k => hH k f hfi hfp)
  calc
    _ ≤ eLpNorm (fun z => G.cutoffMaximal χ (L.low f) z +
        ∑' k, G.cutoffMaximal χ (L.band k f) z) p volume :=
      eLpNorm_mono_enorm (by simpa only [enorm_eq_self] using hrec)
    _ ≤ eLpNorm (G.cutoffMaximal χ (L.low f)) p volume +
        eLpNorm (fun z => ∑' k, G.cutoffMaximal χ (L.band k f) z) p volume :=
      eLpNorm_add_le hmL.stronglyMeasurable.aestronglyMeasurable
        (Measurable.tsum hmH).stronglyMeasurable.aestronglyMeasurable (by exact_mod_cast hp)
    _ ≤ (CL : ℝ≥0∞) * eLpNorm f p volume +
        ((CH : ℝ≥0∞) * ∑' k, dyadicWeight (-η) k) * eLpNorm f p volume :=
      add_le_add (hCL f hfi hfp) hsum
    _ = _ := by rw [← add_mul, ENNReal.coe_toNNReal hC]

theorem Family.cutoffMaximal_continuous_tests_of_geometric_endpoint_e2 {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (ha : ∀ x ∈ tsupport χ,
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff)
    (hgeometric : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ,
      Integrable f → MemLp f (d + 2 : ℝ≥0) volume →
      eLpNorm (G.cutoffMaximal χ (L.band k f)) (d + 2 : ℝ≥0) volume ≤
        C * dyadicWeight ε k * eLpNorm f (d + 2 : ℝ≥0) volume)
    (p : ℝ≥0) (hp : (d + 2 : ℝ≥0) < p) :
    ∃ C : ℝ≥0, ∀ f : Plane → ℂ, Continuous f → Integrable f → MemLp f p volume →
      (∃ B : ℝ, ∀ x, ‖f x‖ ≤ B) →
      Measurable (G.cutoffMaximal χ f) ∧
        eLpNorm (G.cutoffMaximal χ f) p volume ≤ C * eLpNorm f p volume := by
  obtain ⟨η, hη, CH, hCH⟩ := G.summable_dyadic_estimate_of_geometric_endpoint_e2
    χ hχ hc hχ0 ha hd L hgeometric p hp
  apply G.cutoffMaximal_continuous_tests_of_summable_dyadic_e2 χ hχ.continuous hc
    (fun x hx => (ha x hx).continuousAt) L p (by linarith [NNReal.coe_nonneg (d : ℝ≥0)]) hη CH hCH

end PlanarNikodym
