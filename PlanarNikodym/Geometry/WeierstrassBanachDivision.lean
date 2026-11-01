import PlanarNikodym.Geometry.WeierstrassBanachPreparation

/-! Actual analytic division by a monic polynomial whose lower coefficients vanish at the
base parameter. Both quotient and finite remainder are constructed by the analytic Banach
implicit-function theorem. -/

noncomputable section
open Set Filter
open scoped Topology ENNReal

namespace PlanarNikodym

/-- Remainder plus multiplication of the quotient by a monic polynomial. -/
def weierstrassDivisionOperator (m : ℕ) (a : Fin m → ℝ) :
    WeierstrassFactors m →L[ℝ] WeierstrassSeries :=
  weierstrassGlue m + ∑ i : Fin m, a i • weierstrassFactorShift m i

theorem weierstrassDivisionOperator_apply (m : ℕ) (a : Fin m → ℝ)
    (w : WeierstrassFactors m) :
    weierstrassDivisionOperator m a w =
      (∑ i : Fin m, w.1 i • lp.single ∞ (i : ℕ) (1 : ℝ)) +
        weierstrassPolynomialAction m (a, w.2) := by
  rcases w with ⟨b, u⟩
  simp [weierstrassDivisionOperator, weierstrassGlue_eq,
    weierstrassFactorShift, weierstrassPolynomialAction, add_assoc]

@[simp]
theorem weierstrassDivisionOperator_zero (m : ℕ) :
    weierstrassDivisionOperator m 0 = weierstrassGlue m := by
  apply ContinuousLinearMap.ext
  intro w
  simp [weierstrassDivisionOperator]

/-- Division by a parameter-dependent monic polynomial, with a bounded convergent series as
numerator. There are no division estimates or analytic factorization assumptions. -/
theorem exists_weierstrass_banach_division
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a : E → Fin m → ℝ) (G : E → WeierstrassSeries) (x₀ : E)
    (ha : AnalyticAt ℝ a x₀) (ha₀ : a x₀ = 0) (hG : AnalyticAt ℝ G x₀) :
    ∃ (r : E → Fin m → ℝ) (q : E → WeierstrassSeries),
      AnalyticAt ℝ r x₀ ∧ AnalyticAt ℝ q x₀ ∧
      r x₀ = weierstrassHead m (G x₀) ∧
      q x₀ = weierstrassTail m (G x₀) ∧
      ∀ᶠ x in 𝓝 x₀,
        G x = (∑ i : Fin m, r x i • lp.single ∞ (i : ℕ) (1 : ℝ)) +
          weierstrassPolynomialAction m (a x, q x) := by
  let w₀ := weierstrassSplit m (G x₀)
  let R : E × WeierstrassFactors m → WeierstrassFactors m :=
    fun z => weierstrassSplit m (weierstrassDivisionOperator m (a z.1) z.2 - G z.1)
  have hdiv : AnalyticAt ℝ
      (fun z : E × WeierstrassFactors m => weierstrassDivisionOperator m (a z.1) z.2)
      (x₀, w₀) := by
    simp only [weierstrassDivisionOperator, add_apply, sum_apply, smul_apply]
    change AnalyticAt ℝ
      (fun z : E × WeierstrassFactors m => weierstrassGlue m z.2 +
        ∑ i : Fin m, a z.1 i • weierstrassFactorShift m i z.2) (x₀, w₀)
    refine ((weierstrassGlue m).analyticAt _ |>.comp
      (f := fun z : E × WeierstrassFactors m => z.2) analyticAt_snd).fun_add ?_
    apply Finset.analyticAt_fun_sum
    intro i _
    have hai : AnalyticAt ℝ (fun z : E × WeierstrassFactors m => a z.1 i)
        (x₀, w₀) :=
      AnalyticAt.comp (x := (x₀, w₀)) (f := fun z : E × WeierstrassFactors m => z.1)
        (g := fun x => a x i) (analyticAt_pi_iff.mp ha i) analyticAt_fst
    exact hai.fun_smul ((weierstrassFactorShift m i).analyticAt _ |>.comp
      (f := fun z : E × WeierstrassFactors m => z.2) analyticAt_snd)
  have hR : AnalyticAt ℝ R (x₀, w₀) :=
    (weierstrassSplit m).analyticAt _ |>.comp
      (hdiv.fun_sub (hG.comp (f := fun z : E × WeierstrassFactors m => z.1) analyticAt_fst))
  have hslice : (fun w => R (x₀, w)) = (fun w => w - w₀) := by
    funext w
    change weierstrassSplit m
      (weierstrassDivisionOperator m (a x₀) w - G x₀) = w - w₀
    rw [ha₀, weierstrassDivisionOperator_zero, map_sub]
    rw [← weierstrassSplit_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hR₀ : R (x₀, w₀) = 0 := by
    have := congrFun hslice w₀
    simpa only [sub_self] using this
  have hi : ((fderiv ℝ R (x₀, w₀)).comp
      (ContinuousLinearMap.inr ℝ E (WeierstrassFactors m))).IsInvertible := by
    rw [← fderiv_snd_slice R (x₀, w₀) hR.differentiableAt, hslice]
    have hd : HasFDerivAt (fun w : WeierstrassFactors m => w - w₀)
        (ContinuousLinearMap.id ℝ _) w₀ := (hasFDerivAt_id w₀).sub_const w₀
    rw [hd.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  obtain ⟨w, hw, hw₀, hzero, _⟩ := exists_analytic_implicit R x₀ w₀ hR hR₀ hi
  refine ⟨fun x => (w x).1, fun x => (w x).2,
    analyticAt_fst.comp hw, analyticAt_snd.comp hw,
    congrArg Prod.fst hw₀, congrArg Prod.snd hw₀, ?_⟩
  filter_upwards [hzero] with x hx
  have he : weierstrassDivisionOperator m (a x) (w x) - G x = 0 :=
    (weierstrassSplit m).injective (by simpa only [map_zero] using hx)
  rw [weierstrassDivisionOperator_apply] at he
  exact (sub_eq_zero.mp he).symm

end PlanarNikodym
