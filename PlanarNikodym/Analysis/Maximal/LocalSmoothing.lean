import PlanarNikodym.Analysis.Fourier.FrequencyLocalization
import PlanarNikodym.Analysis.Maximal.DyadicSummation
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! Quantified analytic interfaces and their exponent arithmetic.
The actual jet estimate is constructed in `ScalarJetProvedSmoothing`;
these definitions keep its original frequency and input quantifiers. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym

def smoothingThreshold (d : ℕ) : ℝ≥0 := (d + 1) * (d + 2)

/-- Actual auxiliary derivatives, including the zeroth derivative. -/
def Family.auxiliaryJetNorm {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (f : Plane → ℂ) (p : ℝ≥0) (j : ℕ) : ℝ≥0∞ :=
  eLpNorm (fun q : Parameters 2 d =>
    ‖iteratedFDeriv ℝ j (fun u : Aux d => G.cutoffAverage χ f (q.1, u)) q.2‖) p volume

def Family.scaledJetNorm {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (f : Plane → ℂ) (p : ℝ≥0) (s k : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (s + 1), dyadicWeight (-(j : ℝ)) k * G.auxiliaryJetNorm χ f p j

theorem Family.averageNorm_le_scaledJetNorm {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (f : Plane → ℂ) (p : ℝ≥0) (s k : ℕ) :
    eLpNorm (G.cutoffAverage χ f) p volume ≤ G.scaledJetNorm χ f p s k := by
  have h0 : G.auxiliaryJetNorm χ f p 0 = eLpNorm (G.cutoffAverage χ f) p volume := by
    simp only [auxiliaryJetNorm, norm_iteratedFDeriv_zero, eLpNorm_norm]
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (s + 1)) =>
    zero_le (a := dyadicWeight (-(j : ℝ)) k * G.auxiliaryJetNorm χ f p j))
    (show 0 ∈ Finset.range (s + 1) by simp)
  simpa [scaledJetNorm, dyadicWeight, h0] using h

/-- The finite-jet version of (2.1). Each derivative is normalized by its
frequency cost. The actual construction is in `ScalarJetProvedSmoothing`. -/
def JetSmoothingInput {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (L : FrequencyCutoff) (p : ℝ≥0) (s : ℕ) (ε : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
    G.scaledJetNorm χ (L.band k f) p s k ≤
      C * dyadicWeight (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε) k * eLpNorm f p volume

/-- Scaled Sobolev embedding in the auxiliary variables, with an explicit
finite jet. The input is not the false claim that an arbitrary function's
supremum is controlled by its scalar `Lp` norm. -/
def BandSobolevInput {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (L : FrequencyCutoff) (p : ℝ≥0) (s : ℕ) (δ : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
    eLpNorm (G.cutoffMaximal χ (L.band k f)) p volume ≤
      C * dyadicWeight ((d : ℝ) / (p : ℝ) + δ) k *
        G.scaledJetNorm χ (L.band k f) p s k

def DyadicMaximalEstimate {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (L : FrequencyCutoff) (p : ℝ≥0) (ε : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
    eLpNorm (G.cutoffMaximal χ (L.band k f)) p volume ≤
      C * dyadicWeight (-1 / (p : ℝ) + ε) k * eLpNorm f p volume

/-- Theorem 2.1, conditional on the explicitly stronger jet estimate. -/
theorem theorem_2_1_of_jet_smoothing {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (L : FrequencyCutoff) (p : ℝ≥0) (s : ℕ) (ε : ℝ)
    (h : JetSmoothingInput G χ L p s ε) :
    ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffAverage χ (L.band k f)) p volume ≤
        C * dyadicWeight (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε) k * eLpNorm f p volume := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun k f hi hf =>
    (G.averageNorm_le_scaledJetNorm χ (L.band k f) p s k).trans (hC k f hi hf)⟩

/-- Corollary 2.2: the two losses add, while `d/p` cancels. Constants
remain independent of `k` and `f`. -/
theorem corollary_2_2_of_inputs {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (L : FrequencyCutoff) (p : ℝ≥0) (s : ℕ) (ε δ : ℝ)
    (hS : JetSmoothingInput G χ L p s ε) (hB : BandSobolevInput G χ L p s δ) :
    DyadicMaximalEstimate G χ L p (ε + δ) := by
  obtain ⟨CS, hCS⟩ := hS
  obtain ⟨CB, hCB⟩ := hB
  refine ⟨CB * CS, ?_⟩
  intro k f hi hf
  calc
    _ ≤ (CB : ℝ≥0∞) * dyadicWeight ((d : ℝ) / (p : ℝ) + δ) k *
        G.scaledJetNorm χ (L.band k f) p s k := hCB k f hi hf
    _ ≤ (CB : ℝ≥0∞) * dyadicWeight ((d : ℝ) / (p : ℝ) + δ) k *
        ((CS : ℝ≥0∞) * dyadicWeight (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε) k *
          eLpNorm f p volume) := mul_le_mul_right (hCS k f hi hf) _
    _ = _ := by
      have hexp : (d : ℝ) / (p : ℝ) + δ + (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε) =
          -1 / (p : ℝ) + (ε + δ) := by push_cast; ring
      rw [ENNReal.coe_mul, ← hexp, dyadicWeight_add
        ((d : ℝ) / (p : ℝ) + δ) (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε) k]
      ac_rfl

end PlanarNikodym
