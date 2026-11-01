import PlanarNikodym.Geometry.AnalyticPolynomialGcdStrata
import PlanarNikodym.Geometry.AnalyticFractionPolynomialDivision
import PlanarNikodym.Geometry.CommonAnalyticOpen

/-! A strengthened actual Euclidean stratification: every ambient branch and
every zero test comes from analytic functions on one original common domain.
The coefficients are actual analytic fractions there, rather than analytic
functions on unrelated branch neighborhoods. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure CommonAnalyticPolynomialGcdStratification
    (U V : Set E) (P Q : E → ℝ[X]) extends AnalyticPolynomialGcdStratification V P Q where
  ambient_common : ∀ i, CommonAnalyticOpen U (stratum i).ambient
  coefficient_fraction : ∀ i k, AnalyticFractionOn U (stratum i).ambient
    (fun x => (stratum i).coefficients x k)
  zero_test_fraction : ∀ i k, AnalyticFractionOn U (stratum i).ambient
    (fun x => (stratum i).zeroTests x k)

/-- Finite, disjoint, all-parameter Euclidean branches, with a common original
analytic domain. This includes zero remainders and every degree drop. -/
theorem exists_common_analytic_fraction_gcd_stratification
    {M N : ℕ} (a : E → Fin M → ℝ) (b : E → Fin N → ℝ)
    (U V : Set E) (hU : IsOpen U) (hV : CommonAnalyticOpen U V)
    (ha : ∀ i, AnalyticFractionOn U V (fun x => a x i))
    (hb : ∀ i, AnalyticFractionOn U V (fun x => b x i)) :
    Nonempty (CommonAnalyticPolynomialGcdStratification U V
      (fun x => weierstrassPolynomial (a x)) (fun x => weierstrassPolynomial (b x))) := by
  classical
  induction N using Nat.strong_induction_on generalizing M V with
  | h N ih =>
    have hVo : IsOpen V := hV.isOpen hU
    have hbA : AnalyticOnNhd ℝ b V := by
      intro x hx
      exact analyticAt_pi_iff.mpr (fun i => (hb i).analyticOnNhd hVo hV.subset x hx)
    let R : E → ℝ[X] := fun x =>
      weierstrassPolynomial (a x) %ₘ weierstrassPolynomial (b x)
    have hRbound : ∀ x k, N ≤ k → (R x).coeff k = 0 := by
      intro x k hk
      exact polynomial_monic_remainder_coeff_eq_zero a b x k hk
    have hRfrac (k : ℕ) : AnalyticFractionOn U V (fun x => (R x).coeff k) := by
      exact (analyticFractionOn_polynomial_monic_division_coeff
        (fun y => weierstrassPolynomial (a y)) b U V (M + 1)
        (analyticFractionOn_weierstrassPolynomial_coeff a ha)
        (fun y k hk => Polynomial.coeff_eq_zero_of_natDegree_lt (by
          rw [weierstrassPolynomial_natDegree]; omega)) hb k).2
    have hRanalytic (x : E) (hx : x ∈ V) (k : ℕ) :
        AnalyticAt ℝ (fun y => (R y).coeff k) x := by
      exact (hRfrac k).analyticOnNhd hVo hV.subset x hx
    let W (d : Fin N) : Set E := V ∩ {x | (R x).coeff d ≠ 0}
    have hWcommon (d : Fin N) : CommonAnalyticOpen U (W d) :=
      hV.inter_fraction_ne_zero (hRfrac d)
    have hnorm (d : Fin N) (i : Fin (d : ℕ)) :
        AnalyticFractionOn U (W d) (fun x => polynomialMonicCoefficients R d x i) :=
      analyticFractionOn_polynomialMonicCoefficients R d hRfrac i
    let child (d : Fin N) : CommonAnalyticPolynomialGcdStratification U (W d)
        (fun x => weierstrassPolynomial (b x))
        (fun x => weierstrassPolynomial (polynomialMonicCoefficients R d x)) :=
      Classical.choice (ih d d.isLt b (polynomialMonicCoefficients R d)
        (W d) (hWcommon d) (fun i => (hb i).mono inter_subset_left) (hnorm d))
    letI (d : Fin N) : Fintype (child d).Index := (child d).indexFintype
    let I := Unit ⊕ (Σ d : Fin N, (child d).Index)
    let zeroPiece : AnalyticPolynomialGcdStratumData E :=
      ⟨V ∩ {x | R x = 0}, V, N, b, N, fun x i => (R x).coeff i⟩
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
      cover := ?_
      ambient_common := ?_
      coefficient_fraction := ?_
      zero_test_fraction := ?_ }⟩
    · intro i
      rcases i with u | ⟨d, j⟩
      · refine ⟨hVo, fun x hx => hx.1, hbA, ?_, ?_, ?_⟩
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
          have hxV : x ∈ V := ((child d).ambient_subset_domain j hx).1
          apply analyticAt_pi_iff.mpr
          intro i
          induction i using Fin.addCases with
          | left i =>
            simpa only [pieces, Fin.addCases_left] using
              (analyticAt_pi_iff.mp (htests x hx) i)
          | right i =>
            simp only [pieces, Fin.addCases_right]
            split_ifs
            · exact hRanalytic x hxV i
            · exact analyticAt_const
        · intro x
          constructor
          · rintro ⟨hc, hd⟩
            obtain ⟨hxW, ht⟩ := (htesteq x).mp hc
            refine ⟨hxW, ?_⟩
            intro i
            induction i using Fin.addCases with
            | left i => simpa only [pieces, Fin.addCases_left] using ht i
            | right i =>
              simp only [pieces, Fin.addCases_right]
              split_ifs with hdi
              · exact hd.2 i hdi
              · rfl
          · rintro ⟨hxW, ht⟩
            have hchild : x ∈ ((child d).stratum j).carrier := by
              apply (htesteq x).mpr
              refine ⟨hxW, ?_⟩
              intro i
              simpa only [pieces, Fin.addCases_left] using ht (Fin.castAdd N i)
            refine ⟨hchild, ((child d).ambient_subset_domain j hxW).2, ?_⟩
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
        · have hxW : x ∈ W d := ⟨hx, hd.1⟩
          obtain ⟨j, hj⟩ := ((child d).cover x).mp hxW
          exact ⟨Sum.inr ⟨d, j⟩, hj, hd⟩
      · rintro ⟨i, hi⟩
        rcases i with u | ⟨d, j⟩
        · exact hi.1
        · exact (((child d).cover x).mpr ⟨j, hi.1⟩).1

    · intro i
      rcases i with u | ⟨d, j⟩
      · exact hV
      · exact (child d).ambient_common j
    · intro i k
      rcases i with u | ⟨d, j⟩
      · exact hb k
      · exact (child d).coefficient_fraction j k
    · intro i k
      rcases i with u | ⟨d, j⟩
      · exact hRfrac k
      · induction k using Fin.addCases with
        | left k =>
          simpa only [pieces, Fin.addCases_left] using (child d).zero_test_fraction j k
        | right k =>
          simp only [pieces, Fin.addCases_right]
          split_ifs
          · exact (hRfrac k).mono (fun x hx => ((child d).ambient_subset_domain j hx).1)
          · exact AnalyticFractionOn.const U _ 0

end PlanarNikodym
