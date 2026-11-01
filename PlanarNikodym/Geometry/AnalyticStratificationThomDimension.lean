import PlanarNikodym.Geometry.AnalyticStratificationCylinders
import PlanarNikodym.Geometry.AnalyticPolynomialDerivativeNormalization

/-! A canonical dimension label for every nonempty derivative Thom cell.
An actual nonzero polynomial equality selects a graph; otherwise a selected
cell is a band. The label therefore does not depend on root-chart choices. -/
noncomputable section
open Set Polynomial
open scoped Classical
namespace PlanarNikodym

theorem weierstrass_iterated_derivative_ne_zero_iff {m : ℕ}
    (a : Fin m → ℝ) (k : ℕ) :
    derivative^[k] (weierstrassPolynomial a) ≠ 0 ↔ k ≤ m := by
  constructor
  · intro hn
    by_contra hk
    exact hn (iterate_derivative_eq_zero (by rw [weierstrassPolynomial_natDegree]; omega))
  · intro hk hz
    have ht := weierstrass_iterated_derivative_top_coeff a k hk
    rw [hz, coeff_zero] at ht
    have hn : (m.descFactorial k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hk).ne'
    exact hn ht.symm

def monicDerivativeSignDimensionBit {J : Type} (m : J → ℕ)
    (s : PolynomialDerivativeIndex m → Fin 3) : ℕ := by
  classical
  exact if ∃ q, q.2.val ≤ m q.1 ∧ s q = 1 then 0 else 1

theorem monicDerivativeSignDimensionBit_eq {E J : Type}
    (m : J → ℕ) (a : (j : J) → E → Fin (m j) → ℝ)
    (s : PolynomialDerivativeIndex m → Fin 3) (x : E) :
    monicDerivativeSignDimensionBit m s =
      if ∃ q, polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m q ≠ 0 ∧ s q = 1
      then 0 else 1 := by
  classical
  simp only [monicDerivativeSignDimensionBit, polynomialDerivativeFamily,
    weierstrass_iterated_derivative_ne_zero_iff]

theorem cylindrical_dim_eq_base_add_of_thom_signs
    {E J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J] {n : ℕ}
    (Q : AnalyticStratificationChart E) (c : Fin (n + 2) → E → ℝ)
    (ha : ∀ i, AnalyticOnNhd ℝ (c i) Q.image)
    (hc : ∀ x ∈ Q.image, StrictMono (fun i => c i x))
    (P : E → J → ℝ[X]) (s : J → Fin 3) (x : E) (hx : x ∈ Q.image)
    (hder : ∀ j, ∃ k, (P x j).derivative = P x k)
    (hroot : ∀ l : Fin n, ∃ j, P x j ≠ 0 ∧ (P x j).eval (c l.castSucc.succ x) = 0)
    (i : Fin n ⊕ Fin (n + 1))
    (hsign : ∀ z ∈ analyticCylindricalCell Q.image c i,
      z.2 ∈ polynomialThomFamilyCell false (P z.1) s) :
    (Q.cylindrical c ha hc i).dim =
      Q.dim + if ∃ j, P x j ≠ 0 ∧ s j = 1 then 0 else 1 := by
  classical
  rcases i with i | i
  · obtain ⟨j, hj, hzero⟩ := hroot i
    have hs : s j = 1 :=
      ((hsign (x, c i.castSucc.succ x) ⟨hx, rfl⟩) j).symm.trans
        (oneDimensionalSign_eq_one.mpr hzero)
    simp only [AnalyticStratificationChart.cylindrical, AnalyticStratificationChart.graph_dim,
      if_pos (show ∃ j, P x j ≠ 0 ∧ s j = 1 from ⟨j, hj, hs⟩), add_zero]
  · have hne : ¬ ∃ j, P x j ≠ 0 ∧ s j = 1 := by
      rintro ⟨j, hj, hs⟩
      have hsingle := polynomialThomFamilyCell_subsingleton_of_nonzero_equality
        (P x) hder s j hs hj
      let l := c i.castSucc x
      let u := c i.succ x
      have hlt : l < u := hc x hx (by change (i : ℕ) < (i : ℕ) + 1; omega)
      let t := (2 * l + u) / 3
      let v := (l + 2 * u) / 3
      have ht : (x, t) ∈ analyticCylindricalCell Q.image c (Sum.inr i) := by
        refine ⟨hx, ?_, ?_⟩ <;> dsimp [t, l, u] at * <;> linarith
      have hv : (x, v) ∈ analyticCylindricalCell Q.image c (Sum.inr i) := by
        refine ⟨hx, ?_, ?_⟩ <;> dsimp [v, l, u] at * <;> linarith
      have he := hsingle (hsign (x, t) ht) (hsign (x, v) hv)
      dsimp [t, v] at he
      linarith
    simp only [AnalyticStratificationChart.cylindrical, AnalyticStratificationChart.band_dim,
      if_neg hne]

end PlanarNikodym
