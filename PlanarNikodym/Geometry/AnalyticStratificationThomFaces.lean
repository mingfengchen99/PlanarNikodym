import PlanarNikodym.Geometry.AnalyticStratificationThomDimension
import PlanarNikodym.Geometry.PolynomialThomFrontier

/-! Canonical dimension labels are monotone along weak-sign faces, and
strictly decrease for two distinct nonempty Thom fibers. This removes any
dependence of the frontier comparison on the choice of root charts. -/
noncomputable section
open Set Polynomial
open scoped Classical
namespace PlanarNikodym

theorem polynomialThomWeakFamilyCell_subsingleton_of_nonzero_equality
    {J : Type} [Fintype J] (P : J → ℝ[X])
    (hder : ∀ j, ∃ k, (P j).derivative = P k) (s : J → Fin 3)
    (j : J) (hj : P j ≠ 0) (hs : s j = 1) :
    (polynomialThomFamilyCell true P s).Subsingleton := by
  apply ordConnected_subsingleton_of_finite
    (polynomialThomFamilyCell_ordConnected true P hder s)
  apply (Polynomial.finite_setOf_isRoot hj).subset
  intro x hx
  simpa [polynomialSignCondition, hs] using hx j

theorem polynomialThomFace_eq_of_source_equality
    {J : Type} [Fintype J] (P : J → ℝ[X])
    (hder : ∀ j, ∃ k, (P j).derivative = P k) (s t : J → Fin 3)
    (hs : (polynomialThomFamilyCell false P s).Nonempty)
    (ht : (polynomialThomFamilyCell false P t).Nonempty)
    (hf : polynomialThomFace t s) (hz : ∃ j, P j ≠ 0 ∧ s j = 1) : s = t := by
  obtain ⟨j, hj, hsj⟩ := hz
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  have hbW : b ∈ polynomialThomFamilyCell true P s := by
    intro k
    apply (polynomialWeakSignCondition_iff _ _).mpr
    exact (hf k).imp (fun he => (hb k).trans he) (fun he => (hb k).trans he)
  have he : a = b := polynomialThomWeakFamilyCell_subsingleton_of_nonzero_equality
    P hder s j hj hsj (polynomialThomFamilyCell_subset_weak P s ha) hbW
  funext k
  have ha' : oneDimensionalSign ((P k).eval b) = s k := by rw [← he]; exact ha k
  exact ha'.symm.trans (hb k)

theorem polynomialThomFace_eq_of_target_no_equality
    {J : Type} (P : J → ℝ[X]) (s t : J → Fin 3)
    (hs : (polynomialThomFamilyCell false P s).Nonempty)
    (ht : (polynomialThomFamilyCell false P t).Nonempty)
    (hf : polynomialThomFace t s) (hz : ¬ ∃ j, P j ≠ 0 ∧ t j = 1) : s = t := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  funext j
  by_cases hj : P j = 0
  · have hs1 : s j = 1 := by simpa [polynomialSignCondition, hj, oneDimensionalSign] using (ha j).symm
    have ht1 : t j = 1 := by simpa [polynomialSignCondition, hj, oneDimensionalSign] using (hb j).symm
    exact hs1.trans ht1.symm
  · rcases hf j with ht1 | he
    · exact False.elim (hz ⟨j, hj, ht1⟩)
    · exact he.symm

theorem polynomialThomFace_strict_dimension_labels
    {J : Type} [Fintype J] (P : J → ℝ[X])
    (hder : ∀ j, ∃ k, (P j).derivative = P k) (s t : J → Fin 3)
    (hs : (polynomialThomFamilyCell false P s).Nonempty)
    (ht : (polynomialThomFamilyCell false P t).Nonempty)
    (hf : polynomialThomFace t s) (hne : s ≠ t) :
    (¬ ∃ j, P j ≠ 0 ∧ s j = 1) ∧ (∃ j, P j ≠ 0 ∧ t j = 1) := by
  refine ⟨fun hz => hne (polynomialThomFace_eq_of_source_equality P hder s t hs ht hf hz), ?_⟩
  by_contra hz
  exact hne (polynomialThomFace_eq_of_target_no_equality P s t hs ht hf hz)

theorem monicDerivativeSignDimensionBit_mono_of_face
    {J : Type} (m : J → ℕ) (s t : PolynomialDerivativeIndex m → Fin 3)
    (hf : polynomialThomFace t s) :
    monicDerivativeSignDimensionBit m t ≤ monicDerivativeSignDimensionBit m s := by
  by_cases hs : ∃ q, q.2.val ≤ m q.1 ∧ s q = 1
  · obtain ⟨q, hq, hsq⟩ := hs
    have htq : t q = 1 := (hf q).elim id (fun he => he.trans hsq)
    have ht : ∃ q, q.2.val ≤ m q.1 ∧ t q = 1 := ⟨q, hq, htq⟩
    have hs' : ∃ q, q.2.val ≤ m q.1 ∧ s q = 1 := ⟨q, hq, hsq⟩
    simp [monicDerivativeSignDimensionBit, hs', ht]
  · simp only [monicDerivativeSignDimensionBit, if_neg hs]
    split_ifs <;> omega

theorem monicDerivativeSignDimensionBit_strict_of_face
    {E J : Type} [Fintype J] (m : J → ℕ)
    (a : (j : J) → E → Fin (m j) → ℝ) (x : E)
    (s t : PolynomialDerivativeIndex m → Fin 3)
    (hs : (polynomialThomFamilyCell false
      (polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m) s).Nonempty)
    (ht : (polynomialThomFamilyCell false
      (polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m) t).Nonempty)
    (hf : polynomialThomFace t s) (hne : s ≠ t) :
    monicDerivativeSignDimensionBit m t < monicDerivativeSignDimensionBit m s := by
  have hder := polynomialDerivativeFamily_stable (fun j => weierstrassPolynomial (a j x)) m
    (fun j => by rw [weierstrassPolynomial_natDegree])
  obtain ⟨hS, hT⟩ := polynomialThomFace_strict_dimension_labels _ hder s t hs ht hf hne
  rw [monicDerivativeSignDimensionBit_eq m a s x, monicDerivativeSignDimensionBit_eq m a t x]
  simp only [if_neg hS, if_pos hT]
  norm_num

end PlanarNikodym
