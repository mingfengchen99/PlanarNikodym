import PlanarNikodym.Analysis.Maximal.E2ExponentSelection
import PlanarNikodym.Analysis.Jets.ScalarJetProvedSmoothing
import PlanarNikodym.Analysis.Sobolev.GeneralBandSobolev

/-! The actual proved high-p estimate, followed by the completed
interpolation step of §2.5. Only the explicitly displayed geometric
endpoint remains a premise in the second theorem. The smooth analogue
and d=1, p>2 require additional arguments and are not asserted here. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym

/-- The high-p endpoint uses the proved jet theorem and the proved
general-dimensional auxiliary Sobolev theorem, without an estimate Input. -/
theorem Family.dyadicMaximalEstimate_proved_e2 {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x)
    (ha : ∀ x ∈ tsupport χ,
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : smoothingThreshold d ≤ p)
    {ε : ℝ} (hε : 0 < ε) : DyadicMaximalEstimate G χ L p ε := by
  have h := corollary_2_2_of_inputs G χ L p d ε 0
    (G.jetSmoothingInput_of_cinematic_support χ hχ hc hχ0 ha hd L p hp d hε)
    (G.bandSobolevInput_aux χ hχ hc (fun x hx => (ha x hx).contDiffAt)
      L p ((smoothingThreshold_one_le d).trans hp) 0 le_rfl)
  simpa only [add_zero] using h

/-- After the geometric endpoint at d+2 is supplied, every finite p>d+2
has a single strictly negative frequency exponent. The interpolation
operator and high-p endpoint are both the actual proved ones. -/
theorem Family.summable_dyadic_estimate_of_geometric_endpoint_e2 {d : ℕ}
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
  obtain ⟨C₁, hC₁⟩ := G.dyadicMaximalEstimate_proved_e2 χ hχ hc hχ0 ha hd L q₁
    (le_max_left _ _) hε₁
  have hq₀eq : ENNReal.ofReal ((d : ℝ) + 2) = ((d + 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [show (d : ℝ) + 2 = ((d + 2 : ℝ≥0) : ℝ) by norm_cast,
      ENNReal.ofReal_coe_nnreal]
  obtain ⟨C, hC⟩ := G.cutoffMaximal_band_dyadic_interpolation_e2 χ hχ.continuous hc
    (fun x hx => (ha x hx).continuousAt) L
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

end PlanarNikodym
