import PlanarNikodym.Geometry.AnalyticMultiplicityRootBranches
import PlanarNikodym.Geometry.AnalyticPolynomialDivision
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Removing a persistent finite-multiplicity root from the actual polynomial.
The quotient is actual monic division and has analytic coefficients. Its degree
strictly drops and it does not vanish on the removed branch. -/

noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual monic division by the power of a parameter-dependent linear factor. -/
def persistentRootQuotient {m : ℕ} (a : E → Fin m → ℝ) (ρ : E → ℝ) (μ : ℕ)
    (x : E) : ℝ[X] :=
  weierstrassPolynomial (a x) /ₘ (X - C (ρ x)) ^ μ

/-- The quotient's coefficient functions are analytic; no divisibility or
multiplicity assumption is needed for this regularity statement. -/
theorem analyticAt_persistentRootQuotient_coeff
    {m : ℕ} (a : E → Fin m → ℝ) (ρ : E → ℝ) (μ : ℕ) (x₀ : E)
    (ha : AnalyticAt ℝ a x₀) (hρ : AnalyticAt ℝ ρ x₀) (k : ℕ) :
    AnalyticAt ℝ (fun x => (persistentRootQuotient a ρ μ x).coeff k) x₀ := by
  classical
  let A := analyticAtFunctionSubring x₀
  let c : Fin m → A := fun i => ⟨fun x => a x i, analyticAt_pi_iff.mp ha i⟩
  let r : A := ⟨ρ, hρ⟩
  let P : A[X] := X ^ m + ∑ i : Fin m, C (c i) * X ^ (i : ℕ)
  let D : A[X] := (X - C r) ^ μ
  have hD : D.Monic := (monic_X_sub_C r).pow μ
  have hPmap (x : E) : P.map (analyticAtFunctionEval x₀ x) =
      weierstrassPolynomial (a x) := by
    simp only [P, weierstrassPolynomial, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      analyticAtFunctionEval_apply, c]
  have hDmap (x : E) : D.map (analyticAtFunctionEval x₀ x) = (X - C (ρ x)) ^ μ := by
    simp only [D, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, analyticAtFunctionEval_apply, r]
  have he (x : E) : (persistentRootQuotient a ρ μ x).coeff k =
      ((P /ₘ D).coeff k).val x := by
    unfold persistentRootQuotient
    rw [← hPmap x, ← hDmap x, ← Polynomial.map_divByMonic _ hD, Polynomial.coeff_map]
    rfl
  simp_rw [he]
  exact ((P /ₘ D).coeff k).property

/-- The actual vanishing derivative data determine the algebraic multiplicity. -/
theorem polynomial_rootMultiplicity_eq_of_derivative_data
    (P : ℝ[X]) (t : ℝ) (μ : ℕ) (hP : P ≠ 0)
    (hz : ∀ j < μ, (Polynomial.derivative^[j] P).eval t = 0)
    (hn : (Polynomial.derivative^[μ] P).eval t ≠ 0) :
    P.rootMultiplicity t = μ := by
  apply Nat.le_antisymm
  · by_contra h
    exact hn (Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
      (Nat.lt_of_not_ge h))
  · cases μ with
    | zero => exact Nat.zero_le _
    | succ n =>
      apply Nat.succ_le_iff.mpr
      exact Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative hP
        (fun j hj => hz j (Nat.lt_succ_of_le hj))

/-- A monic polynomial is exactly the Weierstrass polynomial of its lower
coefficients when its degree is fixed. -/
theorem weierstrassPolynomial_coeff_of_monic
    (P : ℝ[X]) {n : ℕ} (hP : P.Monic) (hdeg : P.natDegree = n) :
    weierstrassPolynomial (fun i : Fin n => P.coeff i) = P := by
  conv_rhs => rw [hP.as_sum, hdeg]
  simp only [weierstrassPolynomial]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => C (P.coeff i) * X ^ i) n

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Exact derivative multiplicity gives an actual monic quotient with the
predicted smaller degree and no root at the removed branch. -/
theorem persistentRootQuotient_factor
    {m : ℕ} (a : E → Fin m → ℝ) (ρ : E → ℝ) (μ : ℕ) (x : E)
    (hz : ∀ j < μ,
      (Polynomial.derivative^[j] (weierstrassPolynomial (a x))).eval (ρ x) = 0)
    (hn : (Polynomial.derivative^[μ]
      (weierstrassPolynomial (a x))).eval (ρ x) ≠ 0) :
    μ ≤ m ∧
    weierstrassPolynomial (a x) = (X - C (ρ x)) ^ μ * persistentRootQuotient a ρ μ x ∧
    (persistentRootQuotient a ρ μ x).Monic ∧
    (persistentRootQuotient a ρ μ x).natDegree = m - μ ∧
    (persistentRootQuotient a ρ μ x).eval (ρ x) ≠ 0 := by
  let P := weierstrassPolynomial (a x)
  have hP : P.Monic := weierstrassPolynomial_monic (a x)
  have hmul : P.rootMultiplicity (ρ x) = μ :=
    polynomial_rootMultiplicity_eq_of_derivative_data P (ρ x) μ hP.ne_zero hz hn
  have hfactor : P = (X - C (ρ x)) ^ μ * persistentRootQuotient a ρ μ x := by
    simpa only [hmul, persistentRootQuotient, P] using
      (Polynomial.pow_mul_divByMonic_rootMultiplicity_eq P (ρ x)).symm
  have hD : ((X - C (ρ x) : ℝ[X]) ^ μ).Monic := (monic_X_sub_C _).pow μ
  have hdvd : (X - C (ρ x)) ^ μ ∣ P := hmul ▸ P.pow_rootMultiplicity_dvd (ρ x)
  have hdegree : μ ≤ m := by
    have h := Polynomial.natDegree_le_of_dvd hdvd hP.ne_zero
    simpa only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C,
      Nat.mul_one, P, weierstrassPolynomial_natDegree] using h
  refine ⟨hdegree, hfactor, hD.of_mul_monic_left (hfactor ▸ hP), ?_, ?_⟩
  · simp only [persistentRootQuotient, Polynomial.natDegree_divByMonic _ hD,
      weierstrassPolynomial_natDegree, Polynomial.natDegree_pow,
      Polynomial.natDegree_X_sub_C, Nat.mul_one]
  · simpa only [hmul, persistentRootQuotient, P] using
      Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero (ρ x) hP.ne_zero

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Removing a persistent factor preserves precisely the other actual roots. -/
theorem persistentRootQuotient_root_iff
    {m : ℕ} (a : E → Fin m → ℝ) (ρ : E → ℝ) (μ : ℕ) (x : E) (t : ℝ)
    (hμ : 0 < μ)
    (hz : ∀ j < μ,
      (Polynomial.derivative^[j] (weierstrassPolynomial (a x))).eval (ρ x) = 0)
    (hn : (Polynomial.derivative^[μ]
      (weierstrassPolynomial (a x))).eval (ρ x) ≠ 0) :
    (weierstrassPolynomial (a x)).eval t = 0 ↔
      t = ρ x ∨ (persistentRootQuotient a ρ μ x).eval t = 0 := by
  rw [(persistentRootQuotient_factor a ρ μ x hz hn).2.1,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero,
    pow_eq_zero_iff hμ.ne', sub_eq_zero]

/-- A persistent exact positive-multiplicity branch is removed with analytic
monic coefficients. The quotient is constructed, and its degree is strictly
smaller. The hypotheses are actual derivative identities on the parameter
domain, rather than a presumed factorization. -/
theorem exists_analytic_persistent_root_factor
    {m μ : ℕ} (a : E → Fin m → ℝ) (ρ : E → ℝ) (U : Set E)
    (hU : U.Nonempty) (hμ : 0 < μ)
    (ha : AnalyticOnNhd ℝ a U) (hρ : AnalyticOnNhd ℝ ρ U)
    (hz : ∀ x ∈ U, ∀ j < μ,
      (Polynomial.derivative^[j] (weierstrassPolynomial (a x))).eval (ρ x) = 0)
    (hn : ∀ x ∈ U, (Polynomial.derivative^[μ]
      (weierstrassPolynomial (a x))).eval (ρ x) ≠ 0) :
    μ ≤ m ∧ m - μ < m ∧ ∃ q : E → Fin (m - μ) → ℝ,
      AnalyticOnNhd ℝ q U ∧
      (∀ x ∈ U, ∀ i : Fin (m - μ),
        q x i = (persistentRootQuotient a ρ μ x).coeff i) ∧
      ∀ x ∈ U,
        weierstrassPolynomial (a x) =
          (X - C (ρ x)) ^ μ * weierstrassPolynomial (q x) ∧
        (weierstrassPolynomial (q x)).eval (ρ x) ≠ 0 := by
  let q : E → Fin (m - μ) → ℝ :=
    fun x i => (persistentRootQuotient a ρ μ x).coeff i
  have hfac (x : E) (hx : x ∈ U) :=
    persistentRootQuotient_factor a ρ μ x (hz x hx) (hn x hx)
  obtain ⟨x₀, hx₀⟩ := hU
  have hm : μ ≤ m := (hfac x₀ hx₀).1
  refine ⟨hm, Nat.sub_lt (hμ.trans_le hm) hμ, q, ?_, ?_, ?_⟩
  · intro x hx
    apply analyticAt_pi_iff.mpr
    intro i
    exact analyticAt_persistentRootQuotient_coeff a ρ μ x (ha x hx) (hρ x hx) i
  · intro x hx i
    rfl
  · intro x hx
    have he : weierstrassPolynomial (q x) = persistentRootQuotient a ρ μ x :=
      weierstrassPolynomial_coeff_of_monic _ (hfac x hx).2.2.1 (hfac x hx).2.2.2.1
    rw [he]
    exact ⟨(hfac x hx).2.1, (hfac x hx).2.2.2.2⟩

/-- Actual finite-order data produce the candidate root and its obstructions,
together with a proved factor-removal operation on every nonempty subset where
those obstructions vanish. The obstruction-zero case is explicit; no partition
of that parameter locus is presumed. In particular this applies when the
obstructions vanish identically on the constructed open neighborhood. -/
theorem exists_analytic_polynomial_multiplicity_reduction
    [CompleteSpace E] {m : ℕ} (a : E → Fin m → ℝ) (x₀ : E) (t₀ : ℝ) (n : ℕ)
    (ha : AnalyticAt ℝ a x₀)
    (hzero : ∀ j < n + 1,
      (Polynomial.derivative^[j] (weierstrassPolynomial (a x₀))).eval t₀ = 0)
    (hn : (Polynomial.derivative^[n + 1]
      (weierstrassPolynomial (a x₀))).eval t₀ ≠ 0) :
    ∃ (U : Set E) (V : Set ℝ) (ρ : E → ℝ) (b : E → Fin n → ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧
      ρ x₀ = t₀ ∧ MapsTo ρ U V ∧ AnalyticOnNhd ℝ ρ U ∧
      AnalyticOnNhd ℝ b U ∧ b x₀ = 0 ∧
      (∀ x ∈ U, ∀ i : Fin n,
        b x i = (Polynomial.derivative^[i.val]
          (weierstrassPolynomial (a x))).eval (ρ x)) ∧
      (∀ x ∈ U, ∀ t ∈ V,
        (∀ j < n + 1,
          (Polynomial.derivative^[j] (weierstrassPolynomial (a x))).eval t = 0) ↔
            t = ρ x ∧ b x = 0) ∧
      ∀ W ⊆ U, W.Nonempty → (∀ x ∈ W, b x = 0) →
        n + 1 ≤ m ∧ m - (n + 1) < m ∧
        ∃ q : E → Fin (m - (n + 1)) → ℝ,
          AnalyticOnNhd ℝ q W ∧
          (∀ x ∈ W, ∀ i : Fin (m - (n + 1)),
            q x i = (persistentRootQuotient a ρ (n + 1) x).coeff i) ∧
          ∀ x ∈ W,
            weierstrassPolynomial (a x) =
              (X - C (ρ x)) ^ (n + 1) * weierstrassPolynomial (q x) ∧
            (weierstrassPolynomial (q x)).eval (ρ x) ≠ 0 := by
  obtain ⟨U₀, V, ρ, b, hU₀, hx₀, hV, ht, hρ₀, hρV, hρ, hb, hb₀, hbi, hn', he⟩ :=
    exists_analytic_polynomial_multiplicity_root_locus a x₀ t₀ n ha hzero hn
  have hnear : {x | x ∈ U₀ ∧ AnalyticAt ℝ a x} ∈ 𝓝 x₀ :=
    inter_mem (hU₀.mem_nhds hx₀) ha.eventually_analyticAt
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hnear
  refine ⟨U, V, ρ, b, hU, hxU, hV, ht, hρ₀,
    (fun x hx => hρV (hUsub hx).1),
    (fun x hx => hρ x (hUsub hx).1),
    (fun x hx => hb x (hUsub hx).1), hb₀,
    (fun x hx => hbi x (hUsub hx).1),
    (fun x hx => he x (hUsub hx).1), ?_⟩
  intro W hWU hW hbW
  apply exists_analytic_persistent_root_factor a ρ W hW (Nat.zero_lt_succ n)
  · intro x hx
    exact (hUsub (hWU hx)).2
  · intro x hx
    exact hρ x (hUsub (hWU hx)).1
  · intro x hx
    exact (he x (hUsub (hWU hx)).1 (ρ x)
      (hρV (hUsub (hWU hx)).1)).mpr ⟨rfl, hbW x hx⟩
  · intro x hx
    exact hn' x (hUsub (hWU hx)).1 (ρ x) (hρV (hUsub (hWU hx)).1)

end PlanarNikodym
