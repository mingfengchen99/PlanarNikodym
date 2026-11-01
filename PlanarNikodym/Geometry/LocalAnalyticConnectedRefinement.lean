import PlanarNikodym.Geometry.AnalyticSignRefinement
import Mathlib.Analysis.Analytic.Basic

/-! The induction conclusion for actual finite analytic sign refinements.
This is a proposition used for dimension induction, with no certificate
fields or additional mathematical assumptions. -/
noncomputable section
open Set
namespace PlanarNikodym

def LocalAnalyticConnectedRefinement (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ {J : Type} [Fintype J] (f : J → E → ℝ) (x₀ : E),
    (∀ j, AnalyticAt ℝ (f j) x₀) → ∀ O : Set E, IsOpen O → x₀ ∈ O →
    ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ O ∧
      ∃ (κ : Type) (_ : Fintype κ) (g : κ → E → ℝ),
        (∀ k, AnalyticOnNhd ℝ (g k) U) ∧
        (∀ j, ∃ k, EqOn (g k) (f j) U) ∧
        ∀ s, analyticStrongSignCell U g s = ∅ ∨ IsConnected (analyticStrongSignCell U g s)

end PlanarNikodym
