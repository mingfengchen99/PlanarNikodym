import PlanarNikodym.Analysis.Jets.ScalarJetLpReduction

/-! Finite scalar estimates imply the actual normalized auxiliary-jet
estimate. This module performs only the proved finite expansion and
frequency cancellation; its scalar hypothesis is supplied by the scalar
local-smoothing theorem in the final local construction. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators
namespace PlanarNikodym
set_option maxHeartbeats 800000

/-- The finite amplitudes are fixed before the frequency and input. Their
scalar constants can therefore be summed, and every derivative cost is
cancelled by the actual normalization of `scaledJetNorm`. -/
theorem Family.jetSmoothingInput_of_scalarJet_estimates {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : 1 ≤ p) (s : ℕ) (ε : ℝ)
    (hscalar : ∀ ψ : Cutoff d, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ tsupport χ → ∀ m : ℕ,
      ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
        eLpNorm (G.cutoffAverage ψ (scaledFrequencyConvolution
          (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ) ((2 : ℝ) ^ k) f)) p volume ≤
            C * dyadicWeight (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε) k * eLpNorm f p volume) :
    JetSmoothingInput G χ L p s ε := by
  classical
  let a : ℝ := -((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε
  have hj (j : ℕ) : ∃ D : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ,
      Integrable f → MemLp f p volume →
      dyadicWeight (-(j : ℝ)) k * G.auxiliaryJetNorm χ (L.band k f) p j ≤
        D * dyadicWeight a k * eLpNorm f p volume := by
    have hs (α : Fin j → Fin d) (b : ScalarJetPath j) := hscalar
      (G.scalarJetAmplitude χ j (fun i => scalarJetBasis (α i)) b)
      (G.contDiff_scalarJetAmplitude χ hχ hγ j _ b)
      (G.hasCompactSupport_scalarJetAmplitude χ hc j _ b)
      (G.tsupport_scalarJetAmplitude_subset χ j _ b) (scalarJetOrder j b)
    choose C hC using hs
    let B : ScalarJetPath j → ℝ≥0 := fun b =>
      ⟨(2 * Real.pi) ^ scalarJetOrder j b, by positivity⟩
    let D : ℝ≥0 := ∑ α : Fin j → Fin d, ∑ b : ScalarJetPath j, B b * C α b
    refine ⟨D, ?_⟩
    intro k f hf hfp
    have hn : G.auxiliaryJetNorm χ (L.band k f) p j ≤
        (D : ℝ≥0∞) * dyadicWeight (j : ℝ) k * dyadicWeight a k * eLpNorm f p volume := by
      calc
        _ ≤ ∑ α : Fin j → Fin d, ∑ b : ScalarJetPath j,
            eLpNorm (G.cutoffAverage
              (G.scalarJetAmplitude χ j (fun i => scalarJetBasis (α i)) b)
              (scalarJetVerticalIter (scalarJetOrder j b) (L.band k f))) p volume :=
          G.auxiliaryJetNorm_le_scalarJet_sum χ hχ hc hγ (L.band_contDiff_infty k hf) p hp j
        _ ≤ ∑ α : Fin j → Fin d, ∑ b : ScalarJetPath j,
            (B b : ℝ≥0∞) * dyadicWeight (j : ℝ) k *
              ((C α b : ℝ≥0∞) * dyadicWeight a k * eLpNorm f p volume) := by
          apply Finset.sum_le_sum
          intro α _
          apply Finset.sum_le_sum
          intro b _
          rw [G.eLpNorm_scalarJetVerticalIter_band _ L hf p]
          have hB : ENNReal.ofReal ((2 * Real.pi) ^ scalarJetOrder j b) = (B b : ℝ≥0∞) := by
            change ENNReal.ofReal ((B b : ℝ≥0) : ℝ) = (B b : ℝ≥0∞)
            exact ENNReal.ofReal_coe_nnreal
          rw [hB]
          exact mul_le_mul (mul_le_mul_right
            (dyadicWeight_mono_exponent (by exact_mod_cast scalarJetOrder_le j b) k) _)
            (hC α b k f hf hfp) zero_le zero_le
        _ = _ := by
          dsimp [D]
          simp only [ENNReal.ofNNReal_finsetSum, ENNReal.coe_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro α _
          apply Finset.sum_congr rfl
          intro b _
          ac_rfl
    calc
      _ ≤ dyadicWeight (-(j : ℝ)) k *
          ((D : ℝ≥0∞) * dyadicWeight (j : ℝ) k * dyadicWeight a k * eLpNorm f p volume) :=
        mul_le_mul_right hn _
      _ = (D : ℝ≥0∞) * (dyadicWeight (-(j : ℝ)) k * dyadicWeight (j : ℝ) k) *
          dyadicWeight a k * eLpNorm f p volume := by ac_rfl
      _ = _ := by rw [← dyadicWeight_add]; simp [dyadicWeight]
  choose D hD using hj
  refine ⟨∑ j ∈ Finset.range (s + 1), D j, ?_⟩
  intro k f hf hfp
  calc
    _ ≤ ∑ j ∈ Finset.range (s + 1),
        (D j : ℝ≥0∞) * dyadicWeight a k * eLpNorm f p volume :=
      Finset.sum_le_sum fun j _ => hD j k f hf hfp
    _ = _ := by simp only [ENNReal.ofNNReal_finsetSum, Finset.sum_mul]; rfl

end PlanarNikodym
