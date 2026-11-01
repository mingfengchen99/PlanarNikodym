import PlanarNikodym.Geometry.AnalyticIntervalSeparation
import PlanarNikodym.Tame.OneDimensionalAnalyticComponents

/-! Actual one-dimensional local finiteness and definability for all
Boolean sign conditions of a finite real analytic germ family. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem ranDefinable_oneDimensional_open_interval (a b : ℝ) :
    RanDefinable {x : Fin 1 → ℝ | x 0 ∈ Ioo a b} :=
  (ranDefinable_lt (ranDefinableFun_const a) (ranDefinableFun_coordinate (0 : Fin 1))).inter
    (ranDefinable_lt (ranDefinableFun_coordinate (0 : Fin 1)) (ranDefinableFun_const b))

/-- Actual finite connected definable cover on the open interior of the
compact interval. Endpoints are removed without adding any assumption. -/
theorem exists_oneDimensional_open_analytic_sign_cover {ι : Type*} [Fintype ι]
    (I : Interval) (f : ι → ℝ → ℝ) (hf : ∀ i, AnalyticOnNhd ℝ (f i) I.carrier)
    (Q : (ι → Fin 3) → Prop) :
    ∃ (S : Finset ℝ) (C : (S → Fin 3) → Set ℝ),
      (∀ σ, IsPreconnected (C σ)) ∧
      (∀ σ, RanDefinable {x : Fin 1 → ℝ | x 0 ∈ C σ}) ∧
      (∀ σ, C σ ⊆ {x | x ∈ Ioo I.left I.right ∧ Q (fun i => oneDimensionalSign (f i x))}) ∧
      {x | x ∈ Ioo I.left I.right ∧ Q (fun i => oneDimensionalSign (f i x))} ⊆ ⋃ σ, C σ := by
  classical
  obtain ⟨S, C, hC, hdef, hsub, hcover⟩ := exists_oneDimensional_analytic_sign_cover I f hf Q
  refine ⟨S, fun σ => C σ ∩ Ioo I.left I.right, ?_, ?_, ?_, ?_⟩
  · intro σ
    exact ((hC σ).ordConnected.inter ordConnected_Ioo).isPreconnected
  · intro σ
    exact (hdef σ).inter (ranDefinable_oneDimensional_open_interval I.left I.right)
  · intro σ x hx
    exact ⟨hx.2, (hsub σ hx.1).2⟩
  · intro x hx
    obtain ⟨σ, hσ⟩ := mem_iUnion.mp (hcover ⟨⟨hx.1.1.le, hx.1.2.le⟩, hx.2⟩)
    exact mem_iUnion.mpr ⟨σ, hσ, hx.1⟩

theorem oneDimensional_open_analytic_sign_components {ι : Type*} [Fintype ι]
    (I : Interval) (f : ι → ℝ → ℝ) (hf : ∀ i, AnalyticOnNhd ℝ (f i) I.carrier)
    (Q : (ι → Fin 3) → Prop) :
    let E := {x | x ∈ Ioo I.left I.right ∧ Q (fun i => oneDimensionalSign (f i x))}
    (componentDomains E).Finite ∧
      ∀ x : ℝ, RanDefinable {y : Fin 1 → ℝ | y 0 ∈ connectedComponentIn E x} := by
  classical
  obtain ⟨S, C, hC, hdef, hsub, hcover⟩ :=
    exists_oneDimensional_open_analytic_sign_cover I f hf Q
  exact ⟨oneDimensional_components_finite_of_finite_cover C hC hsub hcover,
    ranDefinable_oneDimensional_component_of_finite_cover C hC hsub hcover hdef⟩

/-- One neighborhood is selected before every Boolean sign condition.
Each resulting set has finitely many actual connected components, all
definable in the existing restricted analytic structure. -/
theorem exists_local_oneDimensional_semianalytic_components
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (x : ℝ)
    (hf : ∀ i, AnalyticAt ℝ (f i) x) :
    ∃ I : Interval, x ∈ Ioo I.left I.right ∧
      ∀ Q : (ι → Fin 3) → Prop,
        let E := {y | y ∈ Ioo I.left I.right ∧ Q (fun i => oneDimensionalSign (f i y))}
        (componentDomains E).Finite ∧
          ∀ y : ℝ, RanDefinable {z : Fin 1 → ℝ | z 0 ∈ connectedComponentIn E y} := by
  obtain ⟨I, hx, hI⟩ := exists_analytic_interval_neighborhood f x hf
  exact ⟨I, hx, oneDimensional_open_analytic_sign_components I f hI⟩

end PlanarNikodym
