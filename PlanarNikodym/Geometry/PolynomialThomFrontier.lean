import PlanarNikodym.Geometry.PolynomialDerivativeClosure

/-! The precise one-dimensional face relation for Thom cells and the
point-or-open-interval dichotomy. These are consequences of the proved
strict/weak closure formula, not additional decomposition assumptions. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

theorem polynomialWeakSignCondition_iff (s : Fin 3) (r : ℝ) :
    polynomialSignCondition true s r ↔
      oneDimensionalSign r = 1 ∨ oneDimensionalSign r = s := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have he : oneDimensionalSign r = 0 := oneDimensionalSign_eq_zero.mpr hr
    have hle : r ≤ 0 := hr.le
    have hne : r ≠ 0 := hr.ne
    have hn : ¬ 0 ≤ r := not_le.mpr hr
    fin_cases s <;> simp_all [polynomialSignCondition]
    all_goals (constructor <;> intro h <;> linarith)
  · subst r
    fin_cases s <;> norm_num [polynomialSignCondition, oneDimensionalSign]
  · have he : oneDimensionalSign r = 2 := oneDimensionalSign_eq_two.mpr hr
    have hle : 0 ≤ r := hr.le
    have hne : r ≠ 0 := hr.ne'
    have hn : ¬ r ≤ 0 := not_le.mpr hr
    fin_cases s <;> simp_all [polynomialSignCondition]
    all_goals (constructor <;> intro h <;> linarith)

def polynomialThomFace {ι : Type*} (t s : ι → Fin 3) : Prop :=
  ∀ j, t j = 1 ∨ t j = s j

theorem polynomialThomFamilyCell_subset_closure_iff {ι : Type*} [Fintype ι]
    (P : ι → ℝ[X]) (hder : ∀ j, ∃ k, (P j).derivative = P k)
    (s t : ι → Fin 3) (hs : (polynomialThomFamilyCell false P s).Nonempty)
    (ht : (polynomialThomFamilyCell false P t).Nonempty) :
    polynomialThomFamilyCell false P t ⊆ closure (polynomialThomFamilyCell false P s) ↔
      polynomialThomFace t s := by
  rw [polynomialThomFamilyCell_closure P hder s hs]
  constructor
  · intro h j
    obtain ⟨x, hx⟩ := ht
    have hw := (polynomialWeakSignCondition_iff (s j) ((P j).eval x)).mp (h hx j)
    have hxj : oneDimensionalSign ((P j).eval x) = t j := hx j
    simpa only [hxj] using hw
  · intro h x hx j
    apply (polynomialWeakSignCondition_iff _ _).mpr
    exact (h j).imp (fun he => (hx j).trans he) (fun he => (hx j).trans he)

theorem polynomialThomFamilyCell_closure_union {ι : Type*} [Fintype ι]
    (P : ι → ℝ[X]) (hder : ∀ j, ∃ k, (P j).derivative = P k)
    (s : ι → Fin 3) (hs : (polynomialThomFamilyCell false P s).Nonempty) :
    closure (polynomialThomFamilyCell false P s) =
      ⋃ t : {t : ι → Fin 3 // polynomialThomFace t s}, polynomialThomFamilyCell false P t.val := by
  rw [polynomialThomFamilyCell_closure P hder s hs]
  ext x
  constructor
  · intro hx
    let t : ι → Fin 3 := fun j => oneDimensionalSign ((P j).eval x)
    have ht : polynomialThomFace t s :=
      fun j => (polynomialWeakSignCondition_iff _ _).mp (hx j)
    exact mem_iUnion.mpr ⟨⟨t, ht⟩, fun _ => rfl⟩
  · intro hx j
    obtain ⟨t, ht⟩ := mem_iUnion.mp hx
    apply (polynomialWeakSignCondition_iff _ _).mpr
    exact (t.property j).imp (fun he => (ht j).trans he) (fun he => (ht j).trans he)

private theorem isOpen_polynomialStrictSignCondition (P : ℝ[X]) (s : Fin 3)
    (hs : s = 1 → P = 0) : IsOpen {x : ℝ | polynomialSignCondition false s (P.eval x)} := by
  fin_cases s
  · simpa [polynomialSignCondition, Set.preimage, Set.Iio] using
      (isOpen_Iio.preimage P.continuous : IsOpen ((fun x => P.eval x) ⁻¹' Iio 0))
  · have hp : P = 0 := hs rfl
    simp [hp, polynomialSignCondition, oneDimensionalSign]
  · simpa [polynomialSignCondition, Set.preimage, Set.Ioi] using
      (isOpen_Ioi.preimage P.continuous : IsOpen ((fun x => P.eval x) ⁻¹' Ioi 0))

/-- A Thom sign cell is a singleton (or empty) if it imposes a nonzero
polynomial equality; otherwise it is open. Together with order connectedness
this is the point-or-open-interval assertion, including unbounded intervals. -/
theorem polynomialThomFamilyCell_subsingleton_or_open {ι : Type*} [Fintype ι]
    (P : ι → ℝ[X]) (hder : ∀ j, ∃ k, (P j).derivative = P k) (s : ι → Fin 3) :
    (polynomialThomFamilyCell false P s).Subsingleton ∨
      IsOpen (polynomialThomFamilyCell false P s) := by
  classical
  by_cases hz : ∃ j, s j = 1 ∧ P j ≠ 0
  · obtain ⟨j, hs, hp⟩ := hz
    exact Or.inl (polynomialThomFamilyCell_subsingleton_of_nonzero_equality P hder s j hs hp)
  · right
    have he : polynomialThomFamilyCell false P s =
        ⋂ j, {x : ℝ | polynomialSignCondition false (s j) ((P j).eval x)} := by
      ext x
      simp only [polynomialThomFamilyCell, mem_setOf_eq, mem_iInter]
    rw [he]
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_polynomialStrictSignCondition
    intro hs
    by_contra hp
    exact hz ⟨j, hs, hp⟩

end PlanarNikodym
