import PlanarNikodym.Geometry.AnalyticPolynomialDerivativeNormalization
import PlanarNikodym.Geometry.LocalAnalyticPolynomialCylindricalTests
import PlanarNikodym.Geometry.ThomCylindricalLifting

/-! Common analytic base tests for the full literal derivative extension of
monic analytic polynomial germs. On connected sign-invariant base subsets,
every complete derivative sign condition is empty or one connected root
 graph/band, including all collision parameters. -/
noncomputable section
open Set Filter Polynomial Metric
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_local_analytic_derivative_thom_tests
    {J : Type} [Fintype J] (m : J → ℕ) (a : (j : J) → E → Fin (m j) → ℝ)
    (x₀ : E) (ha : ∀ j, AnalyticAt ℝ (a j) x₀) :
    ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∃ (κ : Type) (_ : Fintype κ) (g : κ → E → ℝ),
        (∀ k, AnalyticOnNhd ℝ (g k) (ball x₀ ε)) ∧
        (∀ x ∈ ball x₀ ε, ∀ j t, (weierstrassPolynomial (a j x)).eval t = 0 → |t| < R) ∧
        ∀ C : Set E, C ⊆ ball x₀ ε → IsConnected C →
          (∀ k x, x ∈ C → ∀ y, y ∈ C → oneDimensionalSign (g k x) = oneDimensionalSign (g k y)) →
          ∀ s : PolynomialDerivativeIndex m → Fin 3,
            polynomialCylindricalSignCell C (-R) R
              (fun x => polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m) s = ∅ ∨
            (IsConnected (polynomialCylindricalSignCell C (-R) R
              (fun x => polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m) s) ∧
              ∀ x ∈ C, ∃ t, (x, t) ∈ polynomialCylindricalSignCell C (-R) R
                (fun x => polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m) s) := by
  classical
  let D (q : PolynomialDerivativeIndex m) := m q.1 - q.2.val
  let b (q : PolynomialDerivativeIndex m) := weierstrassIteratedDerivativeCoefficients (a q.1) q.2.val
  have hb (q : PolynomialDerivativeIndex m) : AnalyticAt ℝ (b q) x₀ :=
    analyticAt_weierstrassIteratedDerivativeCoefficients (a q.1) q.2.val x₀ (ha q.1)
  obtain ⟨ε, R, hε, hR, _, hprep⟩ := exists_local_analytic_polynomial_cylindrical_tests D b x₀ hb
  obtain ⟨κ, hκ, g, hg, hlift⟩ := hprep
  have hrootBound (x : E) (hx : x ∈ ball x₀ ε) (j : J) (t : ℝ)
      (ht : (weierstrassPolynomial (a j x)).eval t = 0) : |t| < R := by
    obtain ⟨n, ρ, _, _, _, hbnd, hun, _⟩ := hlift {x}
      (singleton_subset_iff.mpr hx) (isConnected_singleton) (by
        intro k y hy z hz
        simp only [mem_singleton_iff] at hy hz
        subst y; subst z; rfl)
    let q : PolynomialDerivativeIndex m := ⟨j, ⟨0, by omega⟩⟩
    have hn : (weierstrassPolynomial (b q x)).eval t = 0 := by
      have he := weierstrass_iterated_derivative_normalization (a j) 0 x
      simp only [Function.iterate_zero_apply, Nat.descFactorial_zero, Nat.cast_one, C_1, one_mul] at he
      change (weierstrassPolynomial (weierstrassIteratedDerivativeCoefficients (a j) 0 x)).eval t = 0
      rw [← he]
      exact ht
    obtain ⟨i, rfl⟩ := (hun x (mem_singleton x) t).mp ⟨q, hn⟩
    exact abs_lt.mpr (hbnd x (mem_singleton x) i)
  refine ⟨ε, R, hε, hR, κ, hκ, g, hg, hrootBound, ?_⟩
  intro C hCU hC hs
  obtain ⟨n, ρ, _, hρ, hm, hbound, hunion, _, _, hconn, hsign⟩ := hlift C hCU hC hs
  let Q (x : E) := polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m
  let c := analyticRootCuts (-R) R ρ
  have hc := strictMono_analyticRootCuts (-R) R ρ (by linarith) hm hbound
  have hder (x : E) (_ : x ∈ C) : ∀ q, ∃ r, (Q x q).derivative = Q x r :=
    polynomialDerivativeFamily_stable _ m (fun j => (weierstrassPolynomial_natDegree _).le)
  have hroot (x : E) (hx : x ∈ C) (l : Fin n) : ∃ q, Q x q ≠ 0 ∧ (Q x q).eval (ρ l x) = 0 := by
    obtain ⟨q, hq⟩ := (hunion x hx (ρ l x)).mpr ⟨l, rfl⟩
    have hdeg := Polynomial.natDegree_pos_of_eval₂_root (weierstrassPolynomial_monic (b q x)).ne_zero
      (RingHom.id ℝ) hq (fun _ h => h)
    rw [weierstrassPolynomial_natDegree] at hdeg
    have hk : q.2.val ≤ m q.1 := by change 0 < m q.1 - q.2.val at hdeg; omega
    have hcoef : (m q.1).descFactorial q.2.val ≠ 0 := (Nat.descFactorial_pos.mpr hk).ne'
    refine ⟨q, ?_, ?_⟩
    · change derivative^[q.2.val] (weierstrassPolynomial (a q.1 x)) ≠ 0
      rw [weierstrass_iterated_derivative_normalization]
      exact mul_ne_zero (C_ne_zero.mpr (by exact_mod_cast hcoef)) (weierstrassPolynomial_monic _).ne_zero
    · change (derivative^[q.2.val] (weierstrassPolynomial (a q.1 x))).eval (ρ l x) = 0
      rw [weierstrass_iterated_derivative_normalization, eval_mul, eval_C]
      exact mul_eq_zero_of_right _ hq
  have hcompat (i : Fin n ⊕ Fin (n + 1)) (q : PolynomialDerivativeIndex m)
      (z : E × ℝ) (hz : z ∈ analyticCylindricalCell C c i)
      (w : E × ℝ) (hw : w ∈ analyticCylindricalCell C c i) :
      oneDimensionalSign ((Q z.1 q).eval z.2) = oneDimensionalSign ((Q w.1 q).eval w.2) := by
    by_cases hk : q.2.val ≤ m q.1
    · have he (y : E × ℝ) : oneDimensionalSign ((Q y.1 q).eval y.2) =
          oneDimensionalSign ((weierstrassPolynomial (b q y.1)).eval y.2) := by
        simpa only [Q, polynomialDerivativeFamily, b, if_pos hk] using weierstrass_iterated_derivative_sign (a q.1) q.2.val y.1 y.2
      rw [he, he]
      rcases hsign i q with hn | hz' | hp
      · exact (oneDimensionalSign_eq_zero.mpr (hn z hz)).trans (oneDimensionalSign_eq_zero.mpr (hn w hw)).symm
      · exact (oneDimensionalSign_eq_one.mpr (hz' z hz)).trans (oneDimensionalSign_eq_one.mpr (hz' w hw)).symm
      · exact (oneDimensionalSign_eq_two.mpr (hp z hz)).trans (oneDimensionalSign_eq_two.mpr (hp w hw)).symm
    · have he (y : E × ℝ) : Q y.1 q = 0 :=
        iterate_derivative_eq_zero (by rw [weierstrassPolynomial_natDegree]; omega)
      simp only [he, eval_zero]
  intro s
  rcases polynomialCylindricalSignCell_eq_cell_or_empty C (-R) R Q ρ hc hder hroot hcompat s with h | ⟨i, hi⟩
  · exact Or.inl h
  · refine Or.inr ⟨hi.symm ▸ hconn i, ?_⟩
    intro x hx
    obtain ⟨t, ht⟩ := exists_analyticCylindricalCell_fiber_point c hc hx i
    exact ⟨t, hi.symm ▸ ht⟩

end PlanarNikodym
