import PlanarNikodym.Geometry.RegularStratumEquations
import PlanarNikodym.Geometry.AnalyticStratificationClosedWindowLifting
import PlanarNikodym.Geometry.AnalyticImplicit

/-! A derivative Thom graph has an actual regular polynomial equation.
The last vanishing derivative supplies a zero equation whose vertical
derivative is nonzero on the whole sign cell, including collision strata. -/
noncomputable section
open Set Filter Metric Polynomial Module
open scoped Topology
namespace PlanarNikodym

theorem weierstrass_top_derivative_eval_ne_zero {m : ℕ}
    (a : Fin m → ℝ) (t : ℝ) :
    (derivative^[m] (weierstrassPolynomial a)).eval t ≠ 0 := by
  have hd : (derivative^[m] (weierstrassPolynomial a)).natDegree = 0 := by
    have h := natDegree_iterate_derivative (weierstrassPolynomial a) m
    rw [weierstrassPolynomial_natDegree, Nat.sub_self] at h
    omega
  rw [eq_C_of_natDegree_eq_zero hd, eval_C]
  have h := weierstrass_iterated_derivative_top_coeff a m le_rfl
  rw [Nat.sub_self] at h
  rw [h]
  exact_mod_cast (Nat.descFactorial_pos.mpr (le_refl m)).ne'

theorem exists_regular_thom_derivative {E J : Type} [Fintype J]
    (m : J → ℕ) (a : (j : J) → E → Fin (m j) → ℝ)
    (C : Set E) (l u : ℝ) (s : PolynomialDerivativeIndex m → Fin 3)
    (hne : (polynomialCylindricalSignCell C l u
      (fun x => polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m) s).Nonempty)
    (hgraph : ∃ q : PolynomialDerivativeIndex m, q.2.val ≤ m q.1 ∧ s q = 1) :
    ∃ (j : J) (k : ℕ), k < m j ∧
      (∀ z ∈ polynomialCylindricalSignCell C l u
        (fun x => polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m) s,
        (derivative^[k] (weierstrassPolynomial (a j z.1))).eval z.2 = 0) ∧
      ∀ z ∈ polynomialCylindricalSignCell C l u
        (fun x => polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m) s,
        (derivative^[k + 1] (weierstrassPolynomial (a j z.1))).eval z.2 ≠ 0 := by
  classical
  obtain ⟨q, hqm, hqs⟩ := hgraph
  let P (k : ℕ) : Prop := ∃ hk : k < m q.1 + 2, s ⟨q.1, ⟨k, hk⟩⟩ = 1
  let k := Nat.findGreatest P (m q.1)
  have hk : k ≤ m q.1 := Nat.findGreatest_le _
  have hPk : P k := Nat.findGreatest_spec hqm ⟨q.2.isLt, hqs⟩
  obtain ⟨hkb, hks⟩ := hPk
  have hlt : k < m q.1 := by
    by_contra hn
    have he : k = m q.1 := by omega
    obtain ⟨z, hz⟩ := hne
    have hs := hz.2 ⟨q.1, ⟨k, hkb⟩⟩
    rw [hks] at hs
    have hz0 := oneDimensionalSign_eq_one.mp hs
    exact weierstrass_top_derivative_eval_ne_zero (a q.1 z.1) z.2 (by
      simpa only [polynomialDerivativeFamily, he] using hz0)
  have hnPk : ¬ P (k + 1) :=
    Nat.findGreatest_is_greatest (P := P) (n := m q.1) (by change k < k + 1; omega) (by omega)
  refine ⟨q.1, k, hlt, ?_, ?_⟩
  · intro z hz
    have hs := hz.2 ⟨q.1, ⟨k, hkb⟩⟩
    rw [hks] at hs
    exact oneDimensionalSign_eq_one.mp hs
  · intro z hz hzero
    apply hnPk
    refine ⟨by omega, ?_⟩
    have hs := hz.2 ⟨q.1, ⟨k + 1, by omega⟩⟩
    exact hs.symm.trans (oneDimensionalSign_eq_one.mpr hzero)

theorem regular_equations_polynomial_thom_cell
    {E J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [Fintype J]
    (m : J → ℕ) (a : (j : J) → E → Fin (m j) → ℝ)
    (B C : Set E) (hCB : C ⊆ B) (k : ℕ)
    (hbase : RegularStratumEquations (closure B) C k)
    (ha : ∀ j, AnalyticOnNhd ℝ (a j) (closure B)) (l u : ℝ)
    (s : PolynomialDerivativeIndex m → Fin 3) :
    let A := polynomialCylindricalSignCell C l u
      (fun x => polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m) s
    A.Nonempty → RegularStratumEquations (closure (B ×ˢ Ioo l u)) A
      (k + monicDerivativeSignDimensionBit m s) := by
  classical
  dsimp only
  let A := polynomialCylindricalSignCell C l u
    (fun x => polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m) s
  intro hne
  have hproj : Prod.fst '' closure (B ×ˢ Ioo l u) ⊆ closure B := by
    rintro _ ⟨z, hz, rfl⟩
    rw [closure_prod_eq] at hz
    exact hz.1
  have hAproj : Prod.fst '' A ⊆ C := by
    rintro _ ⟨z, hz, rfl⟩
    exact hz.1.1
  have hAV : A ⊆ closure (B ×ˢ Ioo l u) :=
    fun _ hz => subset_closure ⟨hCB hz.1.1, hz.1.2⟩
  by_cases hgraph : ∃ q : PolynomialDerivativeIndex m, q.2.val ≤ m q.1 ∧ s q = 1
  · obtain ⟨j, r, _, hzero, hnonzero⟩ := exists_regular_thom_derivative m a C l u s hne hgraph
    let H : E × ℝ → ℝ := fun z =>
      (derivative^[r] (weierstrassPolynomial (a j z.1))).eval z.2
    have hHa : AnalyticOnNhd ℝ H (closure (B ×ˢ Ioo l u)) := fun z hz =>
      analyticAt_joint_weierstrass_iterated_derivative_eval (a j) r z.1 z.2
        (ha j z.1 (hproj (mem_image_of_mem _ hz)))
    have hv : ∀ z ∈ A, fderiv ℝ H z (0, 1) ≠ 0 := by
      intro z hz
      have hd := fderiv_snd_slice H z (hHa z (hAV hz)).differentiableAt
      have he := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hd
      have hp := ((derivative^[r] (weierstrassPolynomial (a j z.1))).hasDerivAt z.2).deriv
      have heval : fderiv ℝ H z (0, 1) =
          (derivative (derivative^[r] (weierstrassPolynomial (a j z.1)))).eval z.2 := by
        calc
          _ = fderiv ℝ (fun t => H (z.1, t)) z.2 1 := he.symm
          _ = deriv (fun t => H (z.1, t)) z.2 := rfl
          _ = _ := hp
      rw [heval]
      simpa only [Function.iterate_succ_apply'] using hnonzero z hz
    have hout := hbase.lift_graph (closure (B ×ˢ Ioo l u)) A hproj hAproj hAV H hHa hzero hv
    simpa only [monicDerivativeSignDimensionBit, if_pos hgraph, Nat.add_zero] using hout
  · have hout := hbase.lift_band (closure (B ×ˢ Ioo l u)) A hproj hAproj hAV
    simpa only [monicDerivativeSignDimensionBit, if_neg hgraph] using hout

end PlanarNikodym
