import PlanarNikodym.Geometry.AnalyticPolynomialDegreeStrata
import PlanarNikodym.Geometry.PolynomialDerivativeQuotient
import PlanarNikodym.Geometry.PolynomialEuclideanStep

/-! Finite analytic coefficient strata for actual polynomial gcds.
The recursion follows the exact degree of each Euclidean remainder. Each piece
has an open ambient set carrying analytic monic gcd coefficients; the gcd
identity is asserted on the piece, where the degree equations hold.
No connectedness, cell structure or frontier control is claimed. -/

noncomputable section
open Set Filter Polynomial
open scoped Topology

namespace PlanarNikodym

structure AnalyticPolynomialGcdStratumData (E : Type*) where
  carrier : Set E
  ambient : Set E
  degree : ℕ
  coefficients : E → Fin degree → ℝ
  testCount : ℕ
  zeroTests : E → Fin testCount → ℝ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsAnalyticPolynomialGcdStratum
    (P Q : E → ℝ[X]) (s : AnalyticPolynomialGcdStratumData E) : Prop :=
  IsOpen s.ambient ∧ s.carrier ⊆ s.ambient ∧
  AnalyticOnNhd ℝ s.coefficients s.ambient ∧
  AnalyticOnNhd ℝ s.zeroTests s.ambient ∧
  (∀ x, x ∈ s.carrier ↔ x ∈ s.ambient ∧ ∀ i, s.zeroTests x i = 0) ∧
  ∀ x ∈ s.carrier, ∀ D : ℝ[X],
    D ∣ weierstrassPolynomial (s.coefficients x) ↔ D ∣ P x ∧ D ∣ Q x

/-- A finite disjoint cover by actual gcd pieces, with analytic extensions of
the coefficients to specified open ambient neighborhoods. -/
structure AnalyticPolynomialGcdStratification
    (U : Set E) (P Q : E → ℝ[X]) where
  Index : Type
  indexFintype : Fintype Index
  stratum : Index → AnalyticPolynomialGcdStratumData E
  valid : ∀ i, IsAnalyticPolynomialGcdStratum P Q (stratum i)
  ambient_subset_domain : ∀ i, (stratum i).ambient ⊆ U
  degree_le_right : ∀ i x, (stratum i).degree ≤ (Q x).natDegree
  disjoint : Pairwise (fun i j => Disjoint (stratum i).carrier (stratum j).carrier)
  cover : ∀ x, x ∈ U ↔ ∃ i, x ∈ (stratum i).carrier

private theorem analyticGcd_open_coefficient_ne_zero
    (U : Set E) (hU : IsOpen U) (r : E → ℝ[X]) (d : ℕ)
    (hr : ∀ x ∈ U, AnalyticAt ℝ (fun y => (r y).coeff d) x) :
    IsOpen (U ∩ {x | (r x).coeff d ≠ 0}) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact inter_mem (hU.mem_nhds hx.1) ((hr x hx.1).continuousAt.eventually_ne hx.2)

/-- Actual finite gcd stratification for two analytic monic families of fixed
degrees. All pieces, ambient sets and coefficient functions are constructed by
a terminating Euclidean remainder tree. No gcd coefficient regularity or
constant-rank hypothesis is included among the assumptions. -/
theorem exists_analytic_polynomial_gcd_stratification
    {M N : ℕ} (a : E → Fin M → ℝ) (b : E → Fin N → ℝ)
    (U : Set E) (hU : IsOpen U)
    (ha : AnalyticOnNhd ℝ a U) (hb : AnalyticOnNhd ℝ b U) :
    Nonempty (AnalyticPolynomialGcdStratification U
      (fun x => weierstrassPolynomial (a x)) (fun x => weierstrassPolynomial (b x))) := by
  classical
  induction N using Nat.strong_induction_on generalizing M U with
  | h N ih =>
    let R : E → ℝ[X] := fun x =>
      weierstrassPolynomial (a x) %ₘ weierstrassPolynomial (b x)
    have hRbound : ∀ x k, N ≤ k → (R x).coeff k = 0 := by
      intro x k hk
      exact polynomial_monic_remainder_coeff_eq_zero a b x k hk
    have hRanalytic (x : E) (hx : x ∈ U) (k : ℕ) :
        AnalyticAt ℝ (fun y => (R y).coeff k) x := by
      exact (analyticAt_polynomial_monic_division_coeff
        (fun y => weierstrassPolynomial (a y)) b x (M + 1)
        (analyticAt_weierstrassPolynomial_coeff a x (ha x hx))
        (fun y k hk => Polynomial.coeff_eq_zero_of_natDegree_lt (by
          rw [weierstrassPolynomial_natDegree]; omega)) (hb x hx) k).2
    let V (d : Fin N) : Set E := U ∩ {x | (R x).coeff d ≠ 0}
    have hV (d : Fin N) : IsOpen (V d) :=
      analyticGcd_open_coefficient_ne_zero U hU R d (fun x hx => hRanalytic x hx d)
    have hnorm (d : Fin N) :
        AnalyticOnNhd ℝ (polynomialMonicCoefficients R d) (V d) := by
      intro x hx
      exact analyticAt_polynomialMonicCoefficients R d x (hRanalytic x hx.1) hx.2
    let child (d : Fin N) : AnalyticPolynomialGcdStratification (V d)
        (fun x => weierstrassPolynomial (b x))
        (fun x => weierstrassPolynomial (polynomialMonicCoefficients R d x)) :=
      Classical.choice (ih d d.isLt b (polynomialMonicCoefficients R d)
        (V d) (hV d) (fun x hx => hb x hx.1) (hnorm d))
    letI (d : Fin N) : Fintype (child d).Index := (child d).indexFintype
    let I := Unit ⊕ (Σ d : Fin N, (child d).Index)
    let zeroPiece : AnalyticPolynomialGcdStratumData E :=
      ⟨U ∩ {x | R x = 0}, U, N, b, N, fun x i => (R x).coeff i⟩
    let pieces : I → AnalyticPolynomialGcdStratumData E := fun i =>
      match i with
      | Sum.inl _ => zeroPiece
      | Sum.inr ⟨d, j⟩ =>
        { (child d).stratum j with
          carrier := ((child d).stratum j).carrier ∩ polynomialDegreeStratum R d
          testCount := ((child d).stratum j).testCount + N
          zeroTests := fun x => Fin.addCases (((child d).stratum j).zeroTests x)
            (fun k : Fin N => if (d : ℕ) < k then (R x).coeff k else 0) }
    refine ⟨{
      Index := I
      indexFintype := inferInstance
      stratum := pieces
      valid := ?_
      ambient_subset_domain := ?_
      degree_le_right := ?_
      disjoint := ?_
      cover := ?_ }⟩
    · intro i
      rcases i with u | ⟨d, j⟩
      · refine ⟨hU, fun x hx => hx.1, hb, ?_, ?_, ?_⟩
        · intro x hx
          apply analyticAt_pi_iff.mpr
          intro i
          exact hRanalytic x hx i
        · intro x
          constructor
          · rintro ⟨hx, hz⟩
            refine ⟨hx, ?_⟩
            intro i
            change (R x).coeff i = 0
            have hz' : R x = 0 := hz
            rw [hz']
            exact Polynomial.coeff_zero _
          · rintro ⟨hx, ht⟩
            refine ⟨hx, ?_⟩
            apply Polynomial.ext
            intro k
            by_cases hk : k < N
            · exact ht ⟨k, hk⟩
            · exact hRbound x k (Nat.le_of_not_gt hk)
        · intro x hx D
          exact polynomial_common_divisors_of_monic_remainder_zero
            (a x) (b x) hx.2 D
      · obtain ⟨ho, hsub, han, htests, htesteq, hgcd⟩ := (child d).valid j
        refine ⟨ho, fun x hx => hsub hx.1, han, ?_, ?_, ?_⟩
        · intro x hx
          have hxU : x ∈ U := ((child d).ambient_subset_domain j hx).1
          apply analyticAt_pi_iff.mpr
          intro i
          induction i using Fin.addCases with
          | left i =>
            simpa only [pieces, Fin.addCases_left] using
              (analyticAt_pi_iff.mp (htests x hx) i)
          | right i =>
            simp only [pieces, Fin.addCases_right]
            split_ifs
            · exact hRanalytic x hxU i
            · exact analyticAt_const
        · intro x
          constructor
          · rintro ⟨hc, hd⟩
            obtain ⟨hxV, ht⟩ := (htesteq x).mp hc
            refine ⟨hxV, ?_⟩
            intro i
            induction i using Fin.addCases with
            | left i => simpa only [pieces, Fin.addCases_left] using ht i
            | right i =>
              simp only [pieces, Fin.addCases_right]
              split_ifs with hdi
              · exact hd.2 i hdi
              · rfl
          · rintro ⟨hxV, ht⟩
            have hchild : x ∈ ((child d).stratum j).carrier := by
              apply (htesteq x).mpr
              refine ⟨hxV, ?_⟩
              intro i
              simpa only [pieces, Fin.addCases_left] using ht (Fin.castAdd N i)
            refine ⟨hchild, ((child d).ambient_subset_domain j hxV).2, ?_⟩
            intro k hdk
            by_cases hk : k < N
            · have htest := ht (Fin.natAdd ((child d).stratum j).testCount ⟨k, hk⟩)
              simpa only [pieces, Fin.addCases_right, if_pos hdk] using htest
            · exact hRbound x k (Nat.le_of_not_gt hk)
        · intro x hx D
          exact (hgcd x hx.1 D).trans
            (polynomial_common_divisors_of_monic_remainder_stratum a b d x hx.2 D)
    · intro i
      rcases i with u | ⟨d, j⟩
      · exact fun _ hx => hx
      · exact fun _ hx => ((child d).ambient_subset_domain j hx).1
    · intro i x
      rcases i with u | ⟨d, j⟩
      · exact (weierstrassPolynomial_natDegree (b x)).ge
      · have hd : ((child d).stratum j).degree ≤ d := by
          simpa only [weierstrassPolynomial_natDegree] using (child d).degree_le_right j x
        simpa only [pieces, weierstrassPolynomial_natDegree] using hd.trans d.isLt.le
    · intro i j hij
      rw [Set.disjoint_left]
      intro x hxi hxj
      rcases i with u | ⟨d, i⟩ <;> rcases j with v | ⟨e, j⟩
      · exact hij (by cases u; cases v; rfl)
      · have hz : R x = 0 := hxi.2
        have hn : (R x).coeff e ≠ 0 := hxj.2.1
        exact hn (by rw [hz]; simp)
      · have hz : R x = 0 := hxj.2
        have hn : (R x).coeff d ≠ 0 := hxi.2.1
        exact hn (by rw [hz]; simp)
      · by_cases hde : d = e
        · subst e
          have hne : i ≠ j := fun h => hij (by cases h; rfl)
          exact Set.disjoint_left.mp ((child d).disjoint hne) hxi.1 hxj.1
        · exact Set.disjoint_left.mp
            ((polynomial_finite_degree_split R N hRbound).2 hde) hxi.2 hxj.2
    · intro x
      constructor
      · intro hx
        rcases (polynomial_finite_degree_split R N hRbound).1 x with hz | ⟨d, hd⟩
        · exact ⟨Sum.inl (), hx, hz⟩
        · have hxV : x ∈ V d := ⟨hx, hd.1⟩
          obtain ⟨j, hj⟩ := ((child d).cover x).mp hxV
          exact ⟨Sum.inr ⟨d, j⟩, hj, hd⟩
      · rintro ⟨i, hi⟩
        rcases i with u | ⟨d, j⟩
        · exact hi.1
        · exact (((child d).cover x).mpr ⟨j, hi.1⟩).1

end PlanarNikodym
