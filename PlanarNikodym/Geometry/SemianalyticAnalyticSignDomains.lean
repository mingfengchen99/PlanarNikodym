import PlanarNikodym.Geometry.SemianalyticComponentUnions

/-! Analyticity only near the actual closure suffices for genuine global
local-semianalyticity. Outside the closure, an actual empty neighborhood is
used; the arbitrary ambient function extension is never assumed analytic. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace PlanarNikodym

theorem locallySemianalytic_of_sign_description_at_closure
    {n : ℕ} {J : Type} [Fintype J] {A : Set (Fin n → ℝ)}
    (f : J → (Fin n → ℝ) → ℝ) (hf : ∀ j, AnalyticOnNhd ℝ (f j) (closure A))
    (Q : (J → Fin 3) → Prop)
    (hA : ∀ x, x ∈ A ↔ Q (fun j => oneDimensionalSign (f j x))) :
    LocallySemianalytic A := by
  classical
  intro x
  by_cases hx : x ∈ closure A
  · have hnear : {y : Fin n → ℝ | ∀ j, AnalyticAt ℝ (f j) y} ∈ 𝓝 x :=
      Filter.eventually_all.mpr (fun j => (hf j x hx).eventually_analyticAt)
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hnear
    exact ⟨ball x r, isOpen_ball, mem_ball_self hr, J, inferInstance, f,
      fun j y hy => hsub hy j, Q, fun y _ => hA y⟩
  · refine ⟨(closure A)ᶜ, isClosed_closure.isOpen_compl, hx,
      Empty, inferInstance, (fun j => isEmptyElim j), ?_, (fun _ => False), ?_⟩
    · intro j
      exact isEmptyElim j
    · intro y hy
      exact ⟨fun hyA => False.elim (hy (subset_closure hyA)), False.elim⟩

theorem locallySemianalytic_analytic_sublevel
    {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : AnalyticOnNhd ℝ f (closure {x | f x < 0})) :
    LocallySemianalytic {x | f x < 0} := by
  apply locallySemianalytic_of_sign_description_at_closure
    (fun _ : Fin 1 => f) (fun _ => hf) (fun s => s 0 = 0)
  intro x
  exact oneDimensionalSign_eq_zero.symm

end PlanarNikodym
