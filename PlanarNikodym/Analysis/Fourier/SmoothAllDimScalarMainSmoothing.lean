import PlanarNikodym.Analysis.Fourier.SmoothZeroDimMainELpSmoothing
import PlanarNikodym.Analysis.Fourier.E3SmoothPositiveRadialMainELpSmoothing
import PlanarNikodym.Analysis.Fourier.ScalarMainSmoothing

/-! Genuine C-infinity estimates, including zero auxiliary dimension. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators ComplexConjugate
namespace PlanarNikodym

theorem Family.exists_smooth_positive_main_global_smoothing {d : ℕ} (G : Family 2 d) (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x)

    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (ht : ∀ x ∈ tsupport χ, x.1 ∈ Ioo (-1 : ℝ) 1)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    (p : ℝ≥0) (hp : smoothingThreshold d ≤ p) {ε κ : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) (hz : ∀ η : ℝ, η < κ → β η = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ,
      Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffPartialExtension χ L β r f) p volume ≤
        ENNReal.ofReal (C * r ^ (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε)) *
          eLpNorm f p volume := by
  obtain ⟨M, hM⟩ := L.exists_positive_radial_support β hz
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast (smoothingThreshold_one_le d).trans hp
  apply G.exists_partialExtension_global_Lp_of_L1_error χ hχ hc (fun _ _ => hG.contDiffAt) L β hβ p hp1
    (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε)
  intro N
  rcases d with _ | d
  · have hp2 : (2 : ℝ≥0) ≤ p := by simpa [smoothingThreshold] using hp
    obtain ⟨C, R, hC, _hR, hb⟩ := G.exists_smooth_zero_dim_positive_main_eLp_smoothing_nat
      hG χ hχ hc hχ0 hd ht L β hβ hp2 hε hκ hM N
    refine ⟨R, C, hC.le, fun r hr f hf hfp => ?_⟩
    simpa [div_eq_mul_inv] using hb r ((le_max_right 1 R).trans hr) f hf hfp
  · have hpcrit : glyzCriticalNNExponent (d + 1 + 1) ≤ p := by
      rw [glyzCriticalNNExponent_succ_eq_smoothingThreshold]
      exact hp
    obtain ⟨C, R, hC, _hR, hb⟩ := G.exists_e3_positive_radial_main_eLp_smoothing_nat
      hG (Nat.succ_le_succ (Nat.zero_le d)) χ hχ hc hχ0 hd ht L β hβ hpcrit
      hε hκ hM N
    refine ⟨R, C, hC.le, fun r hr f hf hfp => ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using
      hb r ((le_max_right 1 R).trans hr) f hf hfp

theorem Family.exists_smooth_two_sided_main_global_smoothing {d : ℕ} (G : Family 2 d) (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x)

    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (ht : ∀ x ∈ tsupport χ, x.1 ∈ Ioo (-1 : ℝ) 1)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    (p : ℝ≥0) (hp : smoothingThreshold d ≤ p) {ε κ : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) (hz : ∀ η : ℝ, |η| < κ → β η = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ,
      Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffPartialExtension χ L β r f) p volume ≤
        ENNReal.ofReal (C * r ^ (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε)) *
          eLpNorm f p volume := by
  let βp := positiveRadialSymbol κ β
  let βn := negativeRadialSymbol κ β
  have hβp : ContDiff ℝ ∞ βp := contDiff_positiveRadialSymbol κ hβ
  have hβn : ContDiff ℝ ∞ βn := contDiff_negativeRadialSymbol κ hβ
  obtain ⟨Cp, hCp, hpos⟩ := G.exists_smooth_positive_main_global_smoothing hG χ hχ hc hχ0 hd ht
    L βp hβp p hp hε hκ (fun η hη => positiveRadialSymbol_eq_zero hκ hz hη)
  obtain ⟨Cn, hCn, hneg⟩ := G.exists_smooth_positive_main_global_smoothing hG χ hχ hc hχ0 hd ht
    L.centralReflect (fun η => βn (-η)) (hβn.comp contDiff_neg) p hp hε hκ
    (fun η hη => negativeRadialSymbol_eq_zero hκ hz (by linarith))
  refine ⟨Cp + Cn, add_nonneg hCp hCn, ?_⟩
  intro r hr f hf hfp
  have hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x :=
    fun _ _ => hG.continuous.continuousAt
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast (smoothingThreshold_one_le d).trans hp
  have hn := hneg r hr (fun x => conj (f x))
    (integrable_complex_conjugate hf) (memLp_complex_conjugate hfp)
  have he : G.cutoffPartialExtension χ L.centralReflect (fun η => βn (-η)) r
      (fun x => conj (f x)) = fun q => conj (G.cutoffPartialExtension χ L βn r f q) := by
    funext q
    exact G.cutoffPartialExtension_reflect χ hχ.continuous hc hγ L βn hβn.continuous hf r q
  rw [he, eLpNorm_complex_conjugate, eLpNorm_complex_conjugate] at hn
  rw [G.cutoffPartialExtension_radial_split χ hχ.continuous hc hγ L β hβ hf κ r]
  calc
    _ ≤ eLpNorm (G.cutoffPartialExtension χ L βp r f) p volume +
        eLpNorm (G.cutoffPartialExtension χ L βn r f) p volume :=
      eLpNorm_add_le
        (G.e3_stronglyMeasurable_cutoffPartialExtension hG χ hχ.continuous hc L
          hβp.continuous hf r).aestronglyMeasurable
        (G.e3_stronglyMeasurable_cutoffPartialExtension hG χ hχ.continuous hc L
          hβn.continuous hf r).aestronglyMeasurable hp1
    _ ≤ _ := by
      have hh := add_le_add (hpos r hr f hf hfp) hn
      simpa only [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hCp
        (Real.rpow_nonneg (zero_le_one.trans hr) _)) (mul_nonneg hCn
        (Real.rpow_nonneg (zero_le_one.trans hr) _))] using hh

end PlanarNikodym
