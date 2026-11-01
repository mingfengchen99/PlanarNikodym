import PlanarNikodym.Geometry.ContinuousThomRoots
import PlanarNikodym.Geometry.AnalyticGlobalPolynomialRoots

/-! A genuine finite disjoint parameter partition with complete ordered
continuous roots, including all collision parameters. The partition records
the actual root count and the full Thom codes in increasing root order.
Base cells are not asserted connected or to have finitely many components. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

abbrev PolynomialOrderedThomIndex (m : ℕ) :=
  Σ n : Fin (m + 1), Fin n.val → Fin (m + 1) → Fin 3

def polynomialOrderedThomIndex {m : ℕ} (a : Fin m → ℝ) : PolynomialOrderedThomIndex m :=
  ⟨⟨polynomialRealRootCount a, Nat.lt_succ_of_le (polynomialRealRootCount_le a)⟩,
    fun k => polynomialThomCode (weierstrassPolynomial a) m
      (orderedPolynomialRealRoot a (polynomialRealRootCount a) k)⟩

def polynomialThomBaseCell {E : Type*} {m : ℕ} (a : E → Fin m → ℝ)
    (U : Set E) (i : PolynomialOrderedThomIndex m) : Set E :=
  {x | x ∈ U ∧ polynomialOrderedThomIndex (a x) = i}

theorem polynomialThomBaseCell_pairwiseDisjoint {E : Type*} {m : ℕ}
    (a : E → Fin m → ℝ) (U : Set E) :
    Pairwise (fun i j : PolynomialOrderedThomIndex m =>
      Disjoint (polynomialThomBaseCell a U i) (polynomialThomBaseCell a U j)) := by
  intro i j hij
  exact Set.disjoint_left.mpr (fun _ hi hj => hij (hi.2.symm.trans hj.2))

theorem polynomialThomBaseCell_cover {E : Type*} {m : ℕ}
    (a : E → Fin m → ℝ) (U : Set E) :
    (⋃ i : PolynomialOrderedThomIndex m, polynomialThomBaseCell a U i) = U := by
  ext x
  exact ⟨fun hx => by obtain ⟨i, hi⟩ := mem_iUnion.mp hx; exact hi.1,
    fun hx => mem_iUnion.mpr ⟨polynomialOrderedThomIndex (a x), hx, rfl⟩⟩

theorem polynomialOrderedThomIndex_root {E : Type*} {m : ℕ}
    (a : E → Fin m → ℝ) (x : E)
    (k : Fin (polynomialOrderedThomIndex (a x)).1.val) :
    polynomialThomRoot a ((polynomialOrderedThomIndex (a x)).2 k) x =
      orderedPolynomialRealRoot (a x) (polynomialRealRootCount (a x)) k := by
  let t := orderedPolynomialRealRoot (a x) (polynomialRealRootCount (a x)) k
  have ht : (weierstrassPolynomial (a x)).eval t = 0 :=
    ((orderedPolynomialRealRoot_spec (a x) _ rfl).2 t).mpr ⟨k, rfl⟩
  have hx : x ∈ polynomialThomRootDomain a ((polynomialOrderedThomIndex (a x)).2 k) :=
    ⟨t, ht, rfl⟩
  exact ((polynomialThomRoot_graph_iff a _ hx t).mp ⟨ht, rfl⟩).symm

theorem polynomialThomBaseCell_mem_domain {E : Type*} {m : ℕ}
    (a : E → Fin m → ℝ) (U : Set E) (i : PolynomialOrderedThomIndex m)
    (k : Fin i.1.val) {x : E} (hx : x ∈ polynomialThomBaseCell a U i) :
    x ∈ polynomialThomRootDomain a (i.2 k) := by
  have hi := hx.2
  cases hi
  let t := orderedPolynomialRealRoot (a x) (polynomialRealRootCount (a x)) k
  exact ⟨t, ((orderedPolynomialRealRoot_spec (a x) _ rfl).2 t).mpr ⟨k, rfl⟩, rfl⟩

theorem polynomialThomBaseCell_ordered_roots {E : Type*} {m : ℕ}
    (a : E → Fin m → ℝ) (U : Set E) (i : PolynomialOrderedThomIndex m)
    {x : E} (hx : x ∈ polynomialThomBaseCell a U i) :
    StrictMono (fun k => polynomialThomRoot a (i.2 k) x) ∧
    ∀ t : ℝ, (weierstrassPolynomial (a x)).eval t = 0 ↔
      ∃ k, t = polynomialThomRoot a (i.2 k) x := by
  have hi := hx.2
  cases hi
  simp_rw [polynomialOrderedThomIndex_root]
  exact orderedPolynomialRealRoot_spec (a x) _ rfl

theorem polynomialOrderedThomIndex_eq_iff {m : ℕ} (a : Fin m → ℝ)
    (i : PolynomialOrderedThomIndex m) :
    polynomialOrderedThomIndex a = i ↔
      polynomialRealRootCount a = i.1.val ∧
        ∀ k : Fin i.1.val,
          polynomialThomCode (weierstrassPolynomial a) m
            (orderedPolynomialRealRoot a i.1.val k) = i.2 k := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, fun _ => rfl⟩
  · rintro ⟨hn, hc⟩
    have hf : (polynomialOrderedThomIndex a).1 = i.1 := Fin.ext hn
    rcases i with ⟨n, s⟩
    dsimp only at hf hc
    apply Sigma.ext hf
    cases hf
    exact heq_of_eq (funext hc)

variable {E : Type*} [TopologicalSpace E]

/-- Every canonical base cell has all its roots continuously parametrized
in strict order. Finiteness and disjointness of the base partition are proved
above and no collision-determinant premise occurs. -/
theorem continuousOn_polynomialThomBaseCell_roots {m : ℕ} (a : E → Fin m → ℝ)
    (U : Set E) (hU : IsOpen U) (ha : ContinuousOn a U)
    (i : PolynomialOrderedThomIndex m) (k : Fin i.1.val) :
    ContinuousOn (polynomialThomRoot a (i.2 k)) (polynomialThomBaseCell a U i) :=
  (continuousOn_polynomialThomRoot a U hU ha (i.2 k)).mono
    (fun _ hx => ⟨hx.1, polynomialThomBaseCell_mem_domain a U i k hx⟩)

end PlanarNikodym
