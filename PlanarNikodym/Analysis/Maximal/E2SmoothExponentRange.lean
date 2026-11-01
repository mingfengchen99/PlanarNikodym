import PlanarNikodym.Analysis.Maximal.E2FrequencySummation
import PlanarNikodym.Analysis.Maximal.E2LpExtension
import PlanarNikodym.Analysis.Jets.E3SmoothJetSmoothing

/-! The proved C∞ high-p endpoint is inserted into the actual sublinear
interpolation, Fourier summation, and ambient Lᵖ extension. The geometric
endpoint E1 is the only unproved estimate in the displayed hypotheses.
The range d=1, 2<p≤3 is not a consequence of this interpolation. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym

theorem Family.smooth_dyadicMaximalEstimate_proved_e2 {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (hdim : 1 ≤ d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : smoothingThreshold d ≤ p)
    {ε : ℝ} (hε : 0 < ε) : DyadicMaximalEstimate G χ L p ε := by
  have h := corollary_2_2_of_inputs G χ L p d ε 0
    (G.e3_jetSmoothingInput_of_cinematic_support hG hdim χ hχ hc hχ0 hd L p hp d hε)
    (G.bandSobolevInput_aux χ hχ hc (fun _ _ => hG.contDiffAt)
      L p ((smoothingThreshold_one_le d).trans hp) 0 le_rfl)
  simpa only [add_zero] using h

theorem Family.smooth_summable_dyadic_estimate_of_geometric_endpoint_e2 {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (hdim : 1 ≤ d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff)
    (hgeometric : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ,
      Integrable f → MemLp f (d + 2 : ℝ≥0) volume →
      eLpNorm (G.cutoffMaximal χ (L.band k f)) (d + 2 : ℝ≥0) volume ≤
        C * dyadicWeight ε k * eLpNorm f (d + 2 : ℝ≥0) volume)
    (p : ℝ≥0) (hp : (d + 2 : ℝ≥0) < p) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ,
      Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffMaximal χ (L.band k f)) p volume ≤
        C * dyadicWeight (-η) k * eLpNorm f p volume := by
  let q₁ : ℝ≥0 := max (smoothingThreshold d) (p + 1)
  have hpq : p < q₁ := lt_of_lt_of_le (lt_add_one p) (le_max_right _ _)
  have hqp : ((d : ℝ) + 2) < (p : ℝ) := by exact_mod_cast hp
  have hpqr : (p : ℝ) < (q₁ : ℝ) := by exact_mod_cast hpq
  obtain ⟨ε₀, ε₁, η, b, hε₀, hε₁, hη, he₀, he₁⟩ :=
    e2_exists_summable_interpolation_exponents (by positivity : 0 < (d : ℝ) + 2) hqp hpqr
  obtain ⟨C₀, hC₀⟩ := hgeometric ε₀ hε₀
  obtain ⟨C₁, hC₁⟩ := G.smooth_dyadicMaximalEstimate_proved_e2 hG hdim χ hχ hc hχ0 hd L q₁
    (le_max_left _ _) hε₁
  have hq₀eq : ENNReal.ofReal ((d : ℝ) + 2) = ((d + 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [show (d : ℝ) + 2 = ((d + 2 : ℝ≥0) : ℝ) by norm_cast,
      ENNReal.ofReal_coe_nnreal]
  obtain ⟨C, hC⟩ := G.cutoffMaximal_band_dyadic_interpolation_e2 χ hχ.continuous hc
    (fun _ _ => hG.continuous.continuousAt) L
    (by positivity : 0 < (d : ℝ) + 2) hqp hpqr C₀.coe_nonneg C₁.coe_nonneg he₀ he₁
    (fun k f hf hfp => by
      simpa only [hq₀eq, ENNReal.ofReal_coe_nnreal] using
        hC₀ k f hf (by simpa only [hq₀eq] using hfp))
    (fun k f hf hfp => by
      simpa only [ENNReal.ofReal_coe_nnreal] using
        hC₁ k f hf (by simpa only [ENNReal.ofReal_coe_nnreal] using hfp))
  refine ⟨η, hη, C, ?_⟩
  intro k f hf hfp
  simpa only [ENNReal.ofReal_coe_nnreal] using
    hC k f hf (by simpa only [ENNReal.ofReal_coe_nnreal] using hfp)

/-- Genuine full ambient Lᵖ extension in the range p>d+2 once E1 is
proved for this cutoff. The output agrees with the original pointwise
maximal operator on every compact continuous test and has the same bound. -/
theorem Family.smooth_Lp_extension_of_geometric_endpoint_e2 {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (hdim : 1 ≤ d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff)
    (hgeometric : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ,
      Integrable f → MemLp f (d + 2 : ℝ≥0) volume →
      eLpNorm (G.cutoffMaximal χ (L.band k f)) (d + 2 : ℝ≥0) volume ≤
        C * dyadicWeight ε k * eLpNorm f (d + 2 : ℝ≥0) volume)
    (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))] (hp : (d + 2 : ℝ≥0) < p) :
    ∃ C : ℝ≥0, ∃ T : Lp ℂ p (volume : Measure Plane) → Lp ℂ p (volume : Measure (Base 2)),
      LipschitzWith C T ∧ T 0 = 0 ∧ (∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
      ∀ (f : Plane → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (hfp : MemLp f p volume),
        (T (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.cutoffMaximalComplex_e2 χ f := by
  obtain ⟨η, hη, CH, hCH⟩ := G.smooth_summable_dyadic_estimate_of_geometric_endpoint_e2
    hG hdim χ hχ hc hχ0 hd L hgeometric p hp
  have hp1 : 1 ≤ p := by linarith [NNReal.coe_nonneg (d : ℝ≥0)]
  obtain ⟨C, hC⟩ := G.cutoffMaximal_continuous_tests_of_summable_dyadic_e2 χ hχ.continuous hc
    (fun _ _ => hG.continuous.continuousAt) L p hp1 hη CH hCH
  refine ⟨C, ?_⟩
  apply G.exists_cutoffMaximal_Lp_extension_e2 χ hχ.continuous hc
    (fun _ _ => hG.continuous.continuousAt) p ENNReal.coe_ne_top C
  intro f hf hfc hfp
  obtain ⟨x₀, hx₀⟩ := hf.norm.exists_forall_ge_of_hasCompactSupport hfc.norm
  exact (hC f hf (hf.integrable_of_hasCompactSupport hfc) hfp ⟨‖f x₀‖, hx₀⟩).2

end PlanarNikodym
