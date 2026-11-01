import PlanarNikodym.Geometry.PolynomialDerivativeClosure

/-! Actual finite derivative sign codes uniquely identify real roots, and
their weak fibers are exactly the same singleton. Multiplicities are allowed. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

def polynomialThomCode (P : ℝ[X]) (N : ℕ) (x : ℝ) : Fin (N + 1) → Fin 3 :=
  fun k => oneDimensionalSign ((derivative^[k.val] P).eval x)

def polynomialThomCodeCell (weak : Bool) (P : ℝ[X]) (N : ℕ)
    (s : Fin (N + 1) → Fin 3) : Set ℝ :=
  polynomialThomFamilyCell weak (fun k : Fin (N + 1) => derivative^[k.val] P) s

theorem polynomialThomCodeCell_ordConnected (weak : Bool) (P : ℝ[X])
    (N : ℕ) (hP : P.natDegree ≤ N) (s : Fin (N + 1) → Fin 3) :
    (polynomialThomCodeCell weak P N s).OrdConnected := by
  let t : ℕ → Fin 3 := fun k => if h : k ≤ N then s ⟨k, by omega⟩ else 1
  have he : polynomialThomCodeCell weak P N s = polynomialThomJetCell weak P N t := by
    ext x
    constructor
    · intro hx k hk
      simpa only [t, dif_pos hk] using hx ⟨k, by omega⟩
    · intro hx k
      have hk : k.val ≤ N := by omega
      simpa only [t, dif_pos hk] using hx k.val hk
  rw [he]
  exact polynomialThomJetCell_ordConnected weak P N hP t

theorem polynomialThomCodeCell_closure (P : ℝ[X]) (N : ℕ) (hP : P.natDegree ≤ N)
    (s : Fin (N + 1) → Fin 3) (hne : (polynomialThomCodeCell false P N s).Nonempty) :
    closure (polynomialThomCodeCell false P N s) = polynomialThomCodeCell true P N s :=
  polynomial_signFamilyCell_closure_of_weak_ordConnected _ s
    (polynomialThomCodeCell_ordConnected true P N hP s) hne

theorem polynomialThomCodeCell_root_singleton (P : ℝ[X]) (N : ℕ)
    (hP : P ≠ 0) (hdegree : P.natDegree ≤ N) (x : ℝ) (hx : P.eval x = 0) :
    polynomialThomCodeCell false P N (polynomialThomCode P N x) = {x} := by
  have hmem : x ∈ polynomialThomCodeCell false P N (polynomialThomCode P N x) :=
    fun _ => rfl
  have hsub : polynomialThomCodeCell false P N (polynomialThomCode P N x) ⊆
      {y | P.IsRoot y} := by
    intro y hy
    have hz := hy (⟨0, by omega⟩ : Fin (N + 1))
    change oneDimensionalSign (P.eval y) = oneDimensionalSign (P.eval x) at hz
    rw [hx] at hz
    apply oneDimensionalSign_eq_one.mp
    simpa [oneDimensionalSign] using hz
  have hsingle := ordConnected_subsingleton_of_finite
    (polynomialThomCodeCell_ordConnected false P N hdegree _)
    ((Polynomial.finite_setOf_isRoot hP).subset hsub)
  exact Set.Subset.antisymm (fun y hy => Set.mem_singleton_iff.mpr (hsingle hy hmem))
    (Set.singleton_subset_iff.mpr hmem)

theorem polynomialThomCodeCell_weak_root_singleton (P : ℝ[X]) (N : ℕ)
    (hP : P ≠ 0) (hdegree : P.natDegree ≤ N) (x : ℝ) (hx : P.eval x = 0) :
    polynomialThomCodeCell true P N (polynomialThomCode P N x) = {x} := by
  have hne : (polynomialThomCodeCell false P N (polynomialThomCode P N x)).Nonempty :=
    ⟨x, fun _ => rfl⟩
  rw [← polynomialThomCodeCell_closure P N hdegree (polynomialThomCode P N x) hne,
    polynomialThomCodeCell_root_singleton P N hP hdegree x hx, closure_singleton]

/-- Repeated real roots are also uniquely identified by their actual full
finite derivative sign vector; no simple-root or discriminant assumption. -/
theorem polynomialThomCode_injective_on_roots (P : ℝ[X]) (N : ℕ)
    (hP : P ≠ 0) (hdegree : P.natDegree ≤ N) :
    InjOn (polynomialThomCode P N) {x | P.eval x = 0} := by
  intro x hx y _ he
  have hy : y ∈ polynomialThomCodeCell false P N (polynomialThomCode P N x) := by
    intro k
    exact (congrFun he k).symm
  rw [polynomialThomCodeCell_root_singleton P N hP hdegree x hx] at hy
  exact (Set.mem_singleton_iff.mp hy).symm

end PlanarNikodym
