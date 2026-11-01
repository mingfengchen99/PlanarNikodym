import PlanarNikodym.Geometry.AnalyticDerivativeThomTests

/-! Add the actual monic boundary polynomials before the derivative extension.
Cells on the prescribed vertical strip are entire Thom cells. -/
noncomputable section
open Set Polynomial Metric
namespace PlanarNikodym
variable {E : Type*}

def stripPolynomialDegree {J : Type*} (m : J → ℕ) : J ⊕ Fin 2 → ℕ :=
  Sum.elim m (fun _ => 1)

def stripPolynomialCoefficients {J : Type*} (m : J → ℕ)
    (a : (j : J) → E → Fin (m j) → ℝ) (r : ℝ) :
    (j : J ⊕ Fin 2) → E → Fin (stripPolynomialDegree m j) → ℝ
  | Sum.inl j => a j
  | Sum.inr b => fun _ _ => if b = 0 then r else -r

def stripLeftDerivativeIndex {J : Type*} (m : J → ℕ) :
    PolynomialDerivativeIndex (stripPolynomialDegree m) := ⟨Sum.inr 0, ⟨0, by change 0 < 3; omega⟩⟩
def stripRightDerivativeIndex {J : Type*} (m : J → ℕ) :
    PolynomialDerivativeIndex (stripPolynomialDegree m) := ⟨Sum.inr 1, ⟨0, by change 0 < 3; omega⟩⟩

@[simp] theorem stripPolynomial_eval_left {J : Type*} (m : J → ℕ)
    (a : (j : J) → E → Fin (m j) → ℝ) (r : ℝ) (x : E) (t : ℝ) :
    (weierstrassPolynomial (stripPolynomialCoefficients m a r (Sum.inr 0) x)).eval t = t + r := by
  simp [stripPolynomialCoefficients, weierstrassPolynomial_eval, stripPolynomialDegree]

@[simp] theorem stripPolynomial_eval_right {J : Type*} (m : J → ℕ)
    (a : (j : J) → E → Fin (m j) → ℝ) (r : ℝ) (x : E) (t : ℝ) :
    (weierstrassPolynomial (stripPolynomialCoefficients m a r (Sum.inr 1) x)).eval t = t - r := by
  simp [stripPolynomialCoefficients, weierstrassPolynomial_eval, stripPolynomialDegree, sub_eq_add_neg]

@[simp] theorem stripDerivative_eval_left {J : Type*} (m : J → ℕ)
    (a : (j : J) → E → Fin (m j) → ℝ) (r : ℝ) (x : E) (t : ℝ) :
    (polynomialDerivativeFamily (fun j => weierstrassPolynomial
      (stripPolynomialCoefficients m a r j x)) (stripPolynomialDegree m)
      (stripLeftDerivativeIndex m)).eval t = t + r := by
  simp only [stripLeftDerivativeIndex, polynomialDerivativeFamily, Function.iterate_zero_apply]
  exact stripPolynomial_eval_left m a r x t

@[simp] theorem stripDerivative_eval_right {J : Type*} (m : J → ℕ)
    (a : (j : J) → E → Fin (m j) → ℝ) (r : ℝ) (x : E) (t : ℝ) :
    (polynomialDerivativeFamily (fun j => weierstrassPolynomial
      (stripPolynomialCoefficients m a r j x)) (stripPolynomialDegree m)
      (stripRightDerivativeIndex m)).eval t = t - r := by
  simp only [stripRightDerivativeIndex, polynomialDerivativeFamily, Function.iterate_zero_apply]
  exact stripPolynomial_eval_right m a r x t

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_fixedStrip_analytic_derivative_thom_tests
    {J : Type} [Fintype J] (m : J → ℕ) (a : (j : J) → E → Fin (m j) → ℝ)
    (x₀ : E) (ha : ∀ j, AnalyticAt ℝ (a j) x₀) (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (κ : Type) (_ : Fintype κ) (g : κ → E → ℝ),
      (∀ k, AnalyticOnNhd ℝ (g k) (ball x₀ ε)) ∧
      ∀ C : Set E, C ⊆ ball x₀ ε → IsConnected C →
        (∀ k x, x ∈ C → ∀ y, y ∈ C → oneDimensionalSign (g k x) = oneDimensionalSign (g k y)) →
        ∀ s : PolynomialDerivativeIndex (stripPolynomialDegree m) → Fin 3,
          let P := fun x => polynomialDerivativeFamily (fun j => weierstrassPolynomial
            (stripPolynomialCoefficients m a r j x)) (stripPolynomialDegree m)
          polynomialCylindricalSignCell C (-r) r P s = ∅ ∨
          (IsConnected (polynomialCylindricalSignCell C (-r) r P s) ∧
            ∀ x ∈ C, ∃ t, (x, t) ∈ polynomialCylindricalSignCell C (-r) r P s) := by
  classical
  have ha' (j : J ⊕ Fin 2) : AnalyticAt ℝ (stripPolynomialCoefficients m a r j) x₀ := by
    rcases j with j | b
    · exact ha j
    · exact analyticAt_const
  obtain ⟨ε, R, hε, _, κ, hκ, g, hg, hb, hlift⟩ :=
    exists_local_analytic_derivative_thom_tests (stripPolynomialDegree m)
      (stripPolynomialCoefficients m a r) x₀ ha'
  have hrR : r < R := by
    have h := hb x₀ (mem_ball_self hε) (Sum.inr 1) r (by rw [stripPolynomial_eval_right]; ring)
    rwa [abs_of_pos hr] at h
  refine ⟨ε, hε, κ, hκ, g, hg, ?_⟩
  intro C hCU hC hs s
  dsimp only
  let P := fun x => polynomialDerivativeFamily (fun j => weierstrassPolynomial
    (stripPolynomialCoefficients m a r j x)) (stripPolynomialDegree m)
  rcases Set.eq_empty_or_nonempty (polynomialCylindricalSignCell C (-r) r P s) with hempty | hne
  · exact Or.inl hempty
  · right
    obtain ⟨w, hw⟩ := hne
    have hleft : s (stripLeftDerivativeIndex m) = 2 := by
      have h := hw.2 (stripLeftDerivativeIndex m)
      simp only [P, stripDerivative_eval_left] at h
      exact h.symm.trans (oneDimensionalSign_eq_two.mpr (by linarith [hw.1.2.1]))
    have hright : s (stripRightDerivativeIndex m) = 0 := by
      have h := hw.2 (stripRightDerivativeIndex m)
      simp only [P, stripDerivative_eval_right] at h
      exact h.symm.trans (oneDimensionalSign_eq_zero.mpr (by linarith [hw.1.2.2]))
    have he : polynomialCylindricalSignCell C (-r) r P s =
        polynomialCylindricalSignCell C (-R) R P s := by
      apply Set.Subset.antisymm
      · intro z hz
        exact ⟨⟨hz.1.1, by linarith [hz.1.2.1], by linarith [hz.1.2.2]⟩, hz.2⟩
      · intro z hz
        have hl := hz.2 (stripLeftDerivativeIndex m)
        have hh := hz.2 (stripRightDerivativeIndex m)
        simp only [P, stripDerivative_eval_left, hleft] at hl
        simp only [P, stripDerivative_eval_right, hright] at hh
        have hl' := oneDimensionalSign_eq_two.mp hl
        have hh' := oneDimensionalSign_eq_zero.mp hh
        exact ⟨⟨hz.1.1, by linarith, by linarith⟩, hz.2⟩
    rcases hlift C hCU hC hs s with h | h
    · exact False.elim (Set.Nonempty.ne_empty ⟨w, hw⟩ (he.trans h))
    · exact he.symm ▸ h

end PlanarNikodym
