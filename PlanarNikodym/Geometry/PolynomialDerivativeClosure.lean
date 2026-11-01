import PlanarNikodym.Geometry.PolynomialThomLemma

/-! An explicit finite derivative-closed extension of any polynomial family.
This constructs the family used by Thom's lemma rather than assuming it. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

def PolynomialDerivativeIndex {ι : Type*} (N : ι → ℕ) :=
  Σ j : ι, Fin (N j + 2)

instance {ι : Type*} [Fintype ι] (N : ι → ℕ) : Fintype (PolynomialDerivativeIndex N) :=
  inferInstanceAs (Fintype (Σ j : ι, Fin (N j + 2)))

def polynomialDerivativeFamily {ι : Type*} (P : ι → ℝ[X]) (N : ι → ℕ)
    (j : PolynomialDerivativeIndex N) : ℝ[X] := derivative^[j.2.val] (P j.1)

@[simp] theorem polynomialDerivativeFamily_original {ι : Type*}
    (P : ι → ℝ[X]) (N : ι → ℕ) (j : ι) :
    polynomialDerivativeFamily P N ⟨j, ⟨0, by omega⟩⟩ = P j := rfl

theorem polynomialDerivativeFamily_stable {ι : Type*}
    (P : ι → ℝ[X]) (N : ι → ℕ) (hN : ∀ j, (P j).natDegree ≤ N j) :
    ∀ j, ∃ k, (polynomialDerivativeFamily P N j).derivative =
      polynomialDerivativeFamily P N k := by
  rintro ⟨j, k⟩
  by_cases hk : k.val + 1 < N j + 2
  · refine ⟨⟨j, ⟨k.val + 1, hk⟩⟩, ?_⟩
    simp only [polynomialDerivativeFamily, Function.iterate_succ_apply']
  · have hz : derivative^[k.val] (P j) = 0 :=
      iterate_derivative_eq_zero (by have := k.isLt; have := hN j; omega)
    exact ⟨⟨j, k⟩, by simp only [polynomialDerivativeFamily, hz, derivative_zero]⟩

theorem polynomialThomFamilyCell_pairwiseDisjoint {ι : Type*}
    (P : ι → ℝ[X]) : Pairwise (fun s t : ι → Fin 3 =>
      Disjoint (polynomialThomFamilyCell false P s) (polynomialThomFamilyCell false P t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hst (funext fun j => (hx j).symm.trans (hy j))

theorem polynomialThomFamilyCell_cover {ι : Type*} (P : ι → ℝ[X]) :
    (⋃ s : ι → Fin 3, polynomialThomFamilyCell false P s) = univ := by
  apply Set.Subset.antisymm (subset_univ _)
  intro x _
  exact mem_iUnion.mpr ⟨fun j => oneDimensionalSign ((P j).eval x), fun _ => rfl⟩

/-- Every finite family has a concrete finite derivative extension whose
sign cells are disjoint, cover the line, are connected when nonempty, and
have exactly the weak-sign closure. This includes empty and constant families. -/
theorem polynomial_derivative_closed_separating_family {ι : Type*} [Fintype ι]
    (P : ι → ℝ[X]) (N : ι → ℕ) (hN : ∀ j, (P j).natDegree ≤ N j) :
    let Q := polynomialDerivativeFamily P N
    Pairwise (fun s t : PolynomialDerivativeIndex N → Fin 3 =>
      Disjoint (polynomialThomFamilyCell false Q s) (polynomialThomFamilyCell false Q t)) ∧
    (⋃ s : PolynomialDerivativeIndex N → Fin 3, polynomialThomFamilyCell false Q s) = univ ∧
    (∀ s, (polynomialThomFamilyCell false Q s).OrdConnected) ∧
    ∀ s, (polynomialThomFamilyCell false Q s).Nonempty →
      closure (polynomialThomFamilyCell false Q s) = polynomialThomFamilyCell true Q s := by
  dsimp only
  have hd := polynomialDerivativeFamily_stable P N hN
  exact ⟨polynomialThomFamilyCell_pairwiseDisjoint _, polynomialThomFamilyCell_cover _,
    polynomialThomFamilyCell_ordConnected false _ hd,
    polynomialThomFamilyCell_closure _ hd⟩

end PlanarNikodym
