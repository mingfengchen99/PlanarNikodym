import PlanarNikodym.Analysis.Maximal.OneAuxiliaryL2
import PlanarNikodym.Analysis.Maximal.E2SmoothExponentRange

/-! The full p>2 range in auxiliary dimension one, using the proved
L2 band endpoint and genuine sublinear interpolation. No geometric
endpoint hypothesis occurs in these conclusions. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym

theorem Family.one_auxiliary_summable_dyadic_estimate (G : Family 2 1)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 1 => G.γ x.1 x.2))
    (χ : Cutoff 1) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff)
    (p : ℝ≥0) (hp : (2 : ℝ≥0) < p) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ,
      Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffMaximal χ (L.band k f)) p volume ≤
        C * dyadicWeight (-η) k * eLpNorm f p volume := by
  let q₁ : ℝ≥0 := max (smoothingThreshold 1) (p + 1)
  have hpq : p < q₁ := lt_of_lt_of_le (lt_add_one p) (le_max_right _ _)
  have hqp : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpqr : (p : ℝ) < (q₁ : ℝ) := by exact_mod_cast hpq
  obtain ⟨ε₀, ε₁, η, b, hε₀, hε₁, hη, he₀, he₁⟩ :=
    e2_exists_summable_interpolation_exponents (by positivity : 0 < (2 : ℝ)) hqp hpqr
  obtain ⟨C₀, hL2⟩ := G.one_auxiliary_band_maximal_L2_proved hG χ hχ hc hd L
  have hC₀ (k : ℕ) (f : Plane → ℂ) (hf : Integrable f) (hfp : MemLp f 2 volume) :
      eLpNorm (G.cutoffMaximal χ (L.band k f)) 2 volume ≤
        C₀ * dyadicWeight ε₀ k * eLpNorm f 2 volume := by
    have hone : (1 : ℝ≥0∞) ≤ dyadicWeight ε₀ k := by
      simpa [dyadicWeight] using dyadicWeight_mono_exponent hε₀.le k
    calc
      _ ≤ C₀ * eLpNorm f 2 volume := hL2 k f hf hfp
      _ = C₀ * 1 * eLpNorm f 2 volume := by rw [mul_one]
      _ ≤ _ := by gcongr
  obtain ⟨C₁, hC₁⟩ := G.smooth_dyadicMaximalEstimate_proved_e2 hG (by norm_num) χ hχ hc hχ0 hd L q₁
    (le_max_left _ _) hε₁
  obtain ⟨C, hC⟩ := G.cutoffMaximal_band_dyadic_interpolation_e2 χ hχ.continuous hc
    (fun _ _ => hG.continuous.continuousAt) L
    (by positivity : 0 < (2 : ℝ)) hqp hpqr C₀.coe_nonneg C₁.coe_nonneg he₀ he₁
    (fun k f hf hfp => by
      norm_num at hfp ⊢
      simpa only [ENNReal.ofReal_coe_nnreal] using hC₀ k f hf hfp)
    (fun k f hf hfp => by
      simpa only [ENNReal.ofReal_coe_nnreal] using
        hC₁ k f hf (by simpa only [ENNReal.ofReal_coe_nnreal] using hfp))
  refine ⟨η, hη, C, ?_⟩
  intro k f hf hfp
  simpa only [ENNReal.ofReal_coe_nnreal] using
    hC k f hf (by simpa only [ENNReal.ofReal_coe_nnreal] using hfp)

/-- Genuine full ambient Lᵖ extension for every p>2 in auxiliary dimension one. The output agrees with the original pointwise
maximal operator on every compact continuous test and has the same bound. -/
theorem Family.one_auxiliary_cutoff_Lp_extension (G : Family 2 1)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 1 => G.γ x.1 x.2))
    (χ : Cutoff 1) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff)
    (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))] (hp : (2 : ℝ≥0) < p) :
    ∃ C : ℝ≥0, ∃ T : Lp ℂ p (volume : Measure Plane) → Lp ℂ p (volume : Measure (Base 2)),
      LipschitzWith C T ∧ T 0 = 0 ∧ (∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
      ∀ (f : Plane → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (hfp : MemLp f p volume),
        (T (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.cutoffMaximalComplex_e2 χ f := by
  obtain ⟨η, hη, CH, hCH⟩ := G.one_auxiliary_summable_dyadic_estimate
    hG χ hχ hc hχ0 hd L p hp
  have hp1 : 1 ≤ p := by linarith
  obtain ⟨C, hC⟩ := G.cutoffMaximal_continuous_tests_of_summable_dyadic_e2 χ hχ.continuous hc
    (fun _ _ => hG.continuous.continuousAt) L p hp1 hη CH hCH
  refine ⟨C, ?_⟩
  apply G.exists_cutoffMaximal_Lp_extension_e2 χ hχ.continuous hc
    (fun _ _ => hG.continuous.continuousAt) p ENNReal.coe_ne_top C
  intro f hf hfc hfp
  obtain ⟨x₀, hx₀⟩ := hf.norm.exists_forall_ge_of_hasCompactSupport hfc.norm
  exact (hC f hf (hf.integrable_of_hasCompactSupport hfc) hfp ⟨‖f x₀‖, hx₀⟩).2

end PlanarNikodym
