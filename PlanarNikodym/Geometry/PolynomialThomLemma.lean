import PlanarNikodym.Geometry.PolynomialThomSigns
import PlanarNikodym.Geometry.FiniteIntervalDensity

/-! Thom's lemma for actual finite polynomial families stable under
differentiation: connected sign cells and their exact weak-sign closures. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

def polynomialThomFamilyCell {ι : Type*} (weak : Bool)
    (P : ι → ℝ[X]) (s : ι → Fin 3) : Set ℝ :=
  {x | ∀ j, polynomialSignCondition weak (s j) ((P j).eval x)}

/-- Differentiation closure is an exact algebraic condition on the supplied
finite family, not a geometric decomposition or connectivity premise. -/
theorem polynomialThomFamilyCell_ordConnected {ι : Type*} [Fintype ι]
    (weak : Bool) (P : ι → ℝ[X])
    (hder : ∀ j, ∃ k, (P j).derivative = P k) (s : ι → Fin 3) :
    (polynomialThomFamilyCell weak P s).OrdConnected := by
  classical
  choose d hd using hder
  let N := Finset.univ.sup (fun j => (P j).natDegree)
  have hN (j : ι) : (P j).natDegree ≤ N := Finset.le_sup (f := fun j => (P j).natDegree) (Finset.mem_univ j)
  have hiter (j : ι) (k : ℕ) : derivative^[k] (P j) = P (d^[k] j) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simpa only [Function.iterate_succ_apply', ih] using hd (d^[k] j)
  have hjet (x : ℝ) (hx : x ∈ polynomialThomFamilyCell weak P s) (j : ι) :
      x ∈ polynomialThomJetCell weak (P j) N (fun k => s (d^[k] j)) := by
    intro k _
    rw [hiter]
    exact hx _
  refine ⟨?_⟩
  intro x hx y hy t ht j
  have hc := polynomialThomJetCell_ordConnected weak (P j) N (hN j)
    (fun k => s (d^[k] j))
  exact (hc.out (hjet x hx j) (hjet y hy j) ht) 0 (Nat.zero_le N)

theorem isClosed_polynomialThomWeakFamilyCell {ι : Type*}
    (P : ι → ℝ[X]) (s : ι → Fin 3) :
    IsClosed (polynomialThomFamilyCell true P s) := by
  have he : polynomialThomFamilyCell true P s =
      ⋂ j, (fun x => (P j).eval x) ⁻¹' {r | polynomialSignCondition true (s j) r} := by
    ext x
    simp only [polynomialThomFamilyCell, mem_setOf_eq, mem_iInter, mem_preimage]
  rw [he]
  exact isClosed_iInter (fun j => (isClosed_polynomialWeakSignCondition (s j)).preimage
    (P j).continuous)

theorem polynomialThomFamilyCell_subset_weak {ι : Type*}
    (P : ι → ℝ[X]) (s : ι → Fin 3) :
    polynomialThomFamilyCell false P s ⊆ polynomialThomFamilyCell true P s :=
  fun _ hx j => polynomialSignCondition_weaken (hx j)

/-- Exact closure formula in Thom's lemma. Nonemptiness is essential:
weakening an inconsistent strict sign vector can create new points. -/
theorem polynomial_signFamilyCell_closure_of_weak_ordConnected {ι : Type*} [Fintype ι]
    (P : ι → ℝ[X]) (s : ι → Fin 3)
    (hweak : (polynomialThomFamilyCell true P s).OrdConnected)
    (hne : (polynomialThomFamilyCell false P s).Nonempty) :
    closure (polynomialThomFamilyCell false P s) = polynomialThomFamilyCell true P s := by
  classical
  obtain ⟨a, ha⟩ := hne
  let Z : Set ℝ := ⋃ j, {x | s j ≠ 1 ∧ (P j).eval x = 0}
  have hZ : Z.Finite := by
    apply Set.finite_iUnion
    intro j
    by_cases hs : s j = 1
    · simpa only [hs, ne_eq, not_true_eq_false, false_and, setOf_false] using finite_empty
    · have hv : (P j).eval a ≠ 0 := polynomialSignCondition_ne_zero hs (ha j)
      have hp : P j ≠ 0 := by intro he; exact hv (by simp [he])
      exact (Polynomial.finite_setOf_isRoot hp).subset (fun _ hx => hx.2)
  have he : polynomialThomFamilyCell false P s =
      polynomialThomFamilyCell true P s \ Z := by
    ext x
    constructor
    · intro hx
      refine ⟨polynomialThomFamilyCell_subset_weak P s hx, ?_⟩
      intro hz
      obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      exact polynomialSignCondition_ne_zero hj.1 (hx j) hj.2
    · rintro ⟨hx, hn⟩ j
      apply polynomialSignCondition_strict_of_weak (hx j)
      intro hs hz
      exact hn (mem_iUnion.mpr ⟨j, hs, hz⟩)
  apply Set.Subset.antisymm
  · exact closure_minimal (polynomialThomFamilyCell_subset_weak P s)
      (isClosed_polynomialThomWeakFamilyCell P s)
  · rw [he]
    exact ordConnected_subset_closure_sdiff_finite
      hweak hZ
      (he ▸ (show (polynomialThomFamilyCell false P s).Nonempty from ⟨a, ha⟩))

theorem polynomialThomFamilyCell_closure {ι : Type*} [Fintype ι]
    (P : ι → ℝ[X]) (hder : ∀ j, ∃ k, (P j).derivative = P k)
    (s : ι → Fin 3) (hne : (polynomialThomFamilyCell false P s).Nonempty) :
    closure (polynomialThomFamilyCell false P s) = polynomialThomFamilyCell true P s :=
  polynomial_signFamilyCell_closure_of_weak_ordConnected P s
    (polynomialThomFamilyCell_ordConnected true P hder s) hne

theorem polynomialThomFamilyCell_connected_or_empty {ι : Type*} [Fintype ι]
    (P : ι → ℝ[X]) (hder : ∀ j, ∃ k, (P j).derivative = P k)
    (s : ι → Fin 3) :
    polynomialThomFamilyCell false P s = ∅ ∨
      IsConnected (polynomialThomFamilyCell false P s) := by
  rcases (polynomialThomFamilyCell false P s).eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, (polynomialThomFamilyCell_ordConnected false P hder s).isPreconnected⟩

theorem polynomialThomFamilyCell_subsingleton_of_nonzero_equality
    {ι : Type*} [Fintype ι] (P : ι → ℝ[X])
    (hder : ∀ j, ∃ k, (P j).derivative = P k) (s : ι → Fin 3)
    (j : ι) (hs : s j = 1) (hp : P j ≠ 0) :
    (polynomialThomFamilyCell false P s).Subsingleton := by
  apply ordConnected_subsingleton_of_finite
    (polynomialThomFamilyCell_ordConnected false P hder s)
  apply (Polynomial.finite_setOf_isRoot hp).subset
  intro x hx
  apply oneDimensionalSign_eq_one.mp
  exact (hx j).trans hs

end PlanarNikodym
