import PlanarNikodym.Tame.DefinableFieldOperations
import PlanarNikodym.Geometry.AnalyticPolynomialDegreeStrata

/-! Exact polynomial Euclidean operations preserve definability of the original
coefficient graphs. This supplies definable tests for the actual degree strata,
without assuming a cell decomposition or connected component theorem. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

def ranDefinableFunctionSubring {ι : Type*} (S : Set (ι → ℝ))
    (hS : RanDefinable S) : Subring ((ι → ℝ) → ℝ) where
  carrier := {f | RanDefinableOn f S}
  zero_mem' := (ranDefinableFun_const 0).ranDefinableOn hS
  one_mem' := (ranDefinableFun_const 1).ranDefinableOn hS
  add_mem' hf hg := hf.add hg hS
  mul_mem' hf hg := hf.mul hg hS
  neg_mem' hf := hf.neg hS

def ranDefinableFunctionEval {ι : Type*} (S : Set (ι → ℝ))
    (hS : RanDefinable S) (x : ι → ℝ) :
    ranDefinableFunctionSubring S hS →+* ℝ :=
  (Pi.evalRingHom (fun _ : ι → ℝ => ℝ) x).comp
    (ranDefinableFunctionSubring S hS).subtype

@[simp] theorem ranDefinableFunctionEval_apply {ι : Type*}
    (S : Set (ι → ℝ)) (hS : RanDefinable S) (x : ι → ℝ)
    (f : ranDefinableFunctionSubring S hS) :
    ranDefinableFunctionEval S hS x f = f.val x := rfl

theorem ranDefinableOn_polynomial_monic_division_coeff {ι : Type*}
    (p : (ι → ℝ) → ℝ[X]) {m : ℕ} (a : (ι → ℝ) → Fin m → ℝ)
    {S : Set (ι → ℝ)} (hS : RanDefinable S) (N : ℕ)
    (hp : ∀ k, RanDefinableOn (fun x => (p x).coeff k) S)
    (hbound : ∀ x k, N ≤ k → (p x).coeff k = 0)
    (ha : ∀ i, RanDefinableOn (fun x => a x i) S) (k : ℕ) :
    RanDefinableOn (fun x => (p x /ₘ weierstrassPolynomial (a x)).coeff k) S ∧
    RanDefinableOn (fun x => (p x %ₘ weierstrassPolynomial (a x)).coeff k) S := by
  classical
  let A := ranDefinableFunctionSubring S hS
  let b : ℕ → A := fun i => ⟨fun x => (p x).coeff i, hp i⟩
  let c : Fin m → A := fun i => ⟨fun x => a x i, ha i⟩
  let P : A[X] := ∑ i ∈ Finset.range N, monomial i (b i)
  let Q : A[X] := X ^ m + ∑ i : Fin m, C (c i) * X ^ (i : ℕ)
  have hQ : Q.Monic := by
    apply (monic_X_pow m).add_of_left
    simpa only [degree_X_pow] using degree_sum_fin_lt c
  have hPmap (x : ι → ℝ) : P.map (ranDefinableFunctionEval S hS x) = p x := by
    ext i
    simp only [P, Polynomial.map_sum, Polynomial.map_monomial,
      ranDefinableFunctionEval_apply, b, finsetSum_coeff, coeff_monomial]
    by_cases hi : i < N
    · simp [hi]
    · simp [hi, hbound x i (Nat.le_of_not_gt hi)]
  have hQmap (x : ι → ℝ) : Q.map (ranDefinableFunctionEval S hS x) =
      weierstrassPolynomial (a x) := by
    simp only [Q, weierstrassPolynomial, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      ranDefinableFunctionEval_apply, c]
  have hdiv (x : ι → ℝ) : (p x /ₘ weierstrassPolynomial (a x)).coeff k =
      ((P /ₘ Q).coeff k).val x := by
    rw [← hPmap x, ← hQmap x, ← Polynomial.map_divByMonic _ hQ, Polynomial.coeff_map]
    rfl
  have hmod (x : ι → ℝ) : (p x %ₘ weierstrassPolynomial (a x)).coeff k =
      ((P %ₘ Q).coeff k).val x := by
    rw [← hPmap x, ← hQmap x, ← Polynomial.map_modByMonic _ hQ, Polynomial.coeff_map]
    rfl
  constructor
  · simp_rw [hdiv]
    exact ((P /ₘ Q).coeff k).property
  · simp_rw [hmod]
    exact ((P %ₘ Q).coeff k).property

theorem ranDefinableOn_polynomialMonicCoefficients {ι : Type*}
    (p : (ι → ℝ) → ℝ[X]) (d : ℕ) {S : Set (ι → ℝ)} (hS : RanDefinable S)
    (hp : ∀ k, RanDefinableOn (fun x => (p x).coeff k) S) (i : Fin d) :
    RanDefinableOn (fun x => polynomialMonicCoefficients p d x i) S :=
  (hp i).div (hp d) hS

theorem ranDefinable_polynomialDegreeStratum {ι : Type*}
    (p : (ι → ℝ) → ℝ[X]) (N d : ℕ) {S : Set (ι → ℝ)} (hS : RanDefinable S)
    (hp : ∀ k, RanDefinableOn (fun x => (p x).coeff k) S)
    (hb : ∀ x k, N ≤ k → (p x).coeff k = 0) :
    RanDefinable (S ∩ polynomialDegreeStratum p d) := by
  classical
  have hz (k : Fin N) : RanDefinable {x | x ∈ S ∧ (d < k → (p x).coeff k = 0)} := by
    by_cases hk : d < k
    · simpa only [hk, true_implies] using (hp k).zeroSet hS
    · simpa only [hk, false_implies, and_true, Set.setOf_mem_eq] using hS
  convert ((hp d).nonzeroSet hS).inter (Set.definable_iInter_of_finite hz) using 1
  ext x
  rw [polynomialDegreeStratum_eq_finite_tests p N d hb]
  simp only [mem_inter_iff, mem_setOf_eq, mem_iInter]
  constructor
  · rintro ⟨hx, hn, hzero⟩
    exact ⟨⟨hx, hn⟩, fun k => ⟨hx, fun hk => hzero k (Finset.mem_range.mpr k.isLt) hk⟩⟩
  · rintro ⟨⟨hx, hn⟩, hzero⟩
    exact ⟨hx, hn, fun k hk hd => (hzero ⟨k, Finset.mem_range.mp hk⟩).2 hd⟩

theorem ranDefinable_polynomialZeroStratum {ι : Type*}
    (p : (ι → ℝ) → ℝ[X]) (N : ℕ) {S : Set (ι → ℝ)} (hS : RanDefinable S)
    (hp : ∀ k, RanDefinableOn (fun x => (p x).coeff k) S)
    (hb : ∀ x k, N ≤ k → (p x).coeff k = 0) :
    RanDefinable {x | x ∈ S ∧ p x = 0} := by
  classical
  convert hS.inter (Set.definable_iInter_of_finite
    (fun k : Fin N => (hp k).zeroSet hS)) using 1
  ext x
  simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hx, hz⟩
    exact ⟨hx, fun k => ⟨hx, by simp [hz]⟩⟩
  · rintro ⟨hx, hz⟩
    refine ⟨hx, Polynomial.ext fun k => ?_⟩
    rw [coeff_zero]
    by_cases hk : k < N
    · exact (hz ⟨k, hk⟩).2
    · exact hb x k (Nat.le_of_not_gt hk)

end PlanarNikodym
