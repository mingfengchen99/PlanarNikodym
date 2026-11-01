import PlanarNikodym.Geometry.ThomRegularEquations

/-! The stronger dimension-induction invariant for D-R1: the actual sign
charts retain ambient regular equations analytic on the common closure
window. The lower-dimensional invariant is discharged by induction. -/
noncomputable section
open Set
namespace PlanarNikodym

def AnalyticRegularSignCells {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (g : I → E → ℝ) (δ : (I → Fin 3) → ℕ) : Prop :=
  ∀ s, (analyticStrongSignCell U g s).Nonempty →
    RegularStratumEquations (closure U) (analyticStrongSignCell U g s) (δ s)

def LocalAnalyticRegularRefinement (d : ℕ) : Prop :=
  ∀ {J : Type} [Fintype J] (f : J → (Fin d → ℝ) → ℝ) (x₀ : Fin d → ℝ),
    (∀ j, AnalyticAt ℝ (f j) x₀) →
    ∀ O : Set (Fin d → ℝ), IsOpen O → x₀ ∈ O →
    ∃ U : Set (Fin d → ℝ), IsOpen U ∧ x₀ ∈ U ∧ closure U ⊆ O ∧
      LocallySemianalytic U ∧
      ∃ (κ : Type) (_ : Fintype κ) (g : κ → (Fin d → ℝ) → ℝ)
        (η : (κ → Fin 3) → ℕ),
        (∀ k, AnalyticOnNhd ℝ (g k) (closure U)) ∧
        (∀ j, ∃ k, EqOn (g k) (f j) U) ∧ AnalyticDimensionedSignCells U g η ∧
        AnalyticRegularSignCells U g η

theorem AnalyticRegularSignCells.sum_refinement
    {E I J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (f : I → E → ℝ) (g : J → E → ℝ)
    (δ : (J → Fin 3) → ℕ) (H : AnalyticRegularSignCells U g δ) :
    AnalyticRegularSignCells U (Sum.elim f g) (fun s => δ (fun j => s (Sum.inr j))) := by
  intro s hne
  have hsub : analyticStrongSignCell U (Sum.elim f g) s ⊆
      analyticStrongSignCell U g (fun j => s (Sum.inr j)) :=
    fun _ hx => ⟨hx.1, fun j => hx.2 (Sum.inr j)⟩
  exact (H _ (hne.mono hsub)).mono hsub

end PlanarNikodym
