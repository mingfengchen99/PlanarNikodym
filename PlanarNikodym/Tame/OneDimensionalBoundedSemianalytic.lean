import PlanarNikodym.Tame.OneDimensionalLocalSemianalytic

/-! Compactness upgrades the actual one-dimensional local sign
partition to bounded sign sets. Analyticity is required only near the
closure of the set, not on a surrounding bounding interval. -/
noncomputable section
open Set
namespace PlanarNikodym

/-- A bounded one-dimensional sign set whose defining finite family is
analytic near its closure is definable and has finitely many actual
connected components, each definable. -/
theorem oneDimensional_bounded_analytic_sign_components
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (Q : (ι → Fin 3) → Prop)
    (hb : Bornology.IsBounded {x | Q (fun i => oneDimensionalSign (f i x))})
    (hf : ∀ i, AnalyticOnNhd ℝ (f i)
      (closure {x | Q (fun i => oneDimensionalSign (f i x))})) :
    let E := {x | Q (fun i => oneDimensionalSign (f i x))}
    RanDefinable {y : Fin 1 → ℝ | y 0 ∈ E} ∧ (componentDomains E).Finite ∧
      ∀ x : ℝ, RanDefinable {y : Fin 1 → ℝ | y 0 ∈ connectedComponentIn E x} := by
  classical
  let E : Set ℝ := {x | Q (fun i => oneDimensionalSign (f i x))}
  choose I hxI hI using fun x : closure E =>
    exists_analytic_interval_neighborhood f x (fun i => hf i x x.2)
  let O (x : closure E) := Ioo (I x).left (I x).right
  obtain ⟨T, hT⟩ := hb.isCompact_closure.elim_finite_subcover O
    (fun _ => isOpen_Ioo) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxI ⟨x, hx⟩⟩)
  choose S C hC hdef hsub hcover using fun a : T =>
    exists_oneDimensional_open_analytic_sign_cover (I a) f (hI a) Q
  let J := (a : T) × (S a → Fin 3)
  let D (j : J) : Set ℝ := C j.1 j.2
  have hD : ∀ j, IsPreconnected (D j) := fun j => hC j.1 j.2
  have hDdef : ∀ j, RanDefinable {y : Fin 1 → ℝ | y 0 ∈ D j} :=
    fun j => hdef j.1 j.2
  have hDsub : ∀ j, D j ⊆ E := fun j _ hx => (hsub j.1 j.2 hx).2
  have hDcover : E ⊆ ⋃ j, D j := by
    intro x hx
    obtain ⟨a, haT, hxa⟩ := mem_iUnion₂.mp (hT (subset_closure hx))
    obtain ⟨σ, hσ⟩ := mem_iUnion.mp (hcover ⟨a, haT⟩ ⟨hxa, hx⟩)
    exact mem_iUnion.mpr ⟨⟨⟨a, haT⟩, σ⟩, hσ⟩
  have hEdef : RanDefinable {y : Fin 1 → ℝ | y 0 ∈ E} := by
    convert Set.definable_iUnion_of_finite hDdef using 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun hy => mem_iUnion.mp (hDcover hy), fun ⟨j, hj⟩ => hDsub j hj⟩
  exact ⟨hEdef, oneDimensional_components_finite_of_finite_cover D hD hDsub hDcover,
    ranDefinable_oneDimensional_component_of_finite_cover D hD hDsub hDcover hDdef⟩

/-- The actual one-dimensional bounded analytic-sublevel seed, with
analyticity only along its closure. No component predicate is assumed. -/
theorem oneDimensional_bounded_analytic_sublevel_components (f : ℝ → ℝ)
    (hb : Bornology.IsBounded {x | f x < 0})
    (hf : AnalyticOnNhd ℝ f (closure {x | f x < 0})) :
    RanDefinable {y : Fin 1 → ℝ | f (y 0) < 0} ∧
      (componentDomains {x | f x < 0}).Finite ∧
      ∀ x : ℝ, RanDefinable
        {y : Fin 1 → ℝ | y 0 ∈ connectedComponentIn {x | f x < 0} x} := by
  have hb' : Bornology.IsBounded {x | (fun σ : Unit → Fin 3 => σ () = 0)
      (fun i => oneDimensionalSign ((fun _ : Unit => f) i x))} := by
    simpa only [oneDimensionalSign_eq_zero] using hb
  have hf' : ∀ i : Unit, AnalyticOnNhd ℝ ((fun _ : Unit => f) i)
      (closure {x | (fun σ : Unit → Fin 3 => σ () = 0)
        (fun i => oneDimensionalSign ((fun _ : Unit => f) i x))}) := by
    intro i
    simpa only [oneDimensionalSign_eq_zero] using hf
  simpa only [oneDimensionalSign_eq_zero, Set.mem_setOf_eq] using
    oneDimensional_bounded_analytic_sign_components
      (fun _ : Unit => f) (fun σ => σ () = 0) hb' hf'

end PlanarNikodym
