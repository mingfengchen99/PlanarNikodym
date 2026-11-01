import PlanarNikodym.Geometry.WeierstrassSequence
import PlanarNikodym.Geometry.AnalyticImplicit
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Analytic preparation in the Banach space of bounded coefficients. The polynomial-times-
series map is genuinely analytic and its derivative at any nonzero multiple of `X^m` is an
explicit continuous linear equivalence, including when `m > 1`. -/

noncomputable section
open Set Filter
open scoped Topology ENNReal

namespace PlanarNikodym

abbrev WeierstrassFactors (m : ℕ) := (Fin m → ℝ) × WeierstrassSeries

/-- Multiplication of a bounded series by a monic polynomial of degree `m`. -/
def weierstrassPolynomialAction (m : ℕ) (w : WeierstrassFactors m) : WeierstrassSeries :=
  weierstrassShift m w.2 + ∑ i : Fin m, w.1 i • weierstrassShift (i : ℕ) w.2

def weierstrassFactorCoefficient (m : ℕ) (i : Fin m) :
    WeierstrassFactors m →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℝ (Fin m → ℝ) WeierstrassSeries)

def weierstrassFactorShift (m n : ℕ) :
    WeierstrassFactors m →L[ℝ] WeierstrassSeries :=
  (weierstrassShift n).comp
    (ContinuousLinearMap.snd ℝ (Fin m → ℝ) WeierstrassSeries)

theorem analyticAt_weierstrassPolynomialAction (m : ℕ) (w : WeierstrassFactors m) :
    AnalyticAt ℝ (weierstrassPolynomialAction m) w := by
  apply ((weierstrassFactorShift m m).analyticAt w).fun_add
  exact Finset.analyticAt_fun_sum Finset.univ (fun i _ =>
    ((weierstrassFactorCoefficient m i).analyticAt w).fun_smul
      ((weierstrassFactorShift m i).analyticAt w))

/-- The exact derivative at the normalized base polynomial and constant unit. -/
def weierstrassLinearization (m : ℕ) (c : ℝ) :
    WeierstrassFactors m →L[ℝ] WeierstrassSeries :=
  (weierstrassGlue m).comp
    ((c • ContinuousLinearMap.fst ℝ (Fin m → ℝ) WeierstrassSeries).prod
      (ContinuousLinearMap.snd ℝ (Fin m → ℝ) WeierstrassSeries))

@[simp]
theorem weierstrassLinearization_apply (m : ℕ) (c : ℝ) (w : WeierstrassFactors m) :
    weierstrassLinearization m c w = weierstrassGlue m (c • w.1, w.2) := rfl

/-- The derivative is invertible for every degree; no simplicity of a scalar root is needed. -/
def weierstrassLinearizationEquiv (m : ℕ) (c : ℝ) (hc : c ≠ 0) :
    WeierstrassFactors m ≃L[ℝ] WeierstrassSeries :=
  (((LinearEquiv.smulOfNeZero ℝ (Fin m → ℝ) c hc).toContinuousLinearEquiv).prodCongr
    (ContinuousLinearEquiv.refl ℝ WeierstrassSeries)).trans (weierstrassSplit m).symm

theorem weierstrassLinearization_isInvertible (m : ℕ) (c : ℝ) (hc : c ≠ 0) :
    (weierstrassLinearization m c).IsInvertible := by
  refine ⟨weierstrassLinearizationEquiv m c hc, ?_⟩
  apply ContinuousLinearMap.ext
  intro w
  rfl

theorem hasFDerivAt_weierstrassPolynomialAction (m : ℕ) (c : ℝ) :
    HasFDerivAt (weierstrassPolynomialAction m) (weierstrassLinearization m c)
      (0, c • lp.single ∞ 0 (1 : ℝ)) := by
  let w₀ : WeierstrassFactors m := (0, c • lp.single ∞ 0 (1 : ℝ))
  have hi (i : Fin m) : HasFDerivAt
      (fun w : WeierstrassFactors m =>
        weierstrassFactorCoefficient m i w • weierstrassFactorShift m i w)
      ((weierstrassFactorCoefficient m i).smulRight (c • lp.single ∞ (i : ℕ) (1 : ℝ))) w₀ := by
    convert! ((weierstrassFactorCoefficient m i).hasFDerivAt).smul
      ((weierstrassFactorShift m i).hasFDerivAt) using 1
    simp [w₀, weierstrassFactorCoefficient, weierstrassFactorShift, map_smul]
  have hs := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin m))) (fun i _ => hi i)
  have hd := ((weierstrassFactorShift m m).hasFDerivAt (x := w₀)).add hs
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro w
  simp [weierstrassFactorCoefficient, weierstrassFactorShift,
    weierstrassGlue_eq, smul_smul, mul_comm, add_comm]

@[simp]
theorem weierstrassPolynomialAction_base (m : ℕ) (c : ℝ) :
    weierstrassPolynomialAction m (0, c • lp.single ∞ 0 (1 : ℝ)) =
      c • lp.single ∞ m (1 : ℝ) := by
  simp [weierstrassPolynomialAction, map_smul]

/-- Multiple-root preparation for an actual analytic family in a Banach space of convergent
coefficients. The coefficient identity is exact locally and the constant coefficient of the
constructed unit remains nonzero. -/
theorem exists_weierstrass_banach_preparation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : E → WeierstrassSeries) (x₀ : E) (m : ℕ) (c : ℝ) (hc : c ≠ 0)
    (hF : AnalyticAt ℝ F x₀) (hF₀ : F x₀ = c • lp.single ∞ m (1 : ℝ)) :
    ∃ (a : E → Fin m → ℝ) (u : E → WeierstrassSeries),
      AnalyticAt ℝ a x₀ ∧ AnalyticAt ℝ u x₀ ∧ a x₀ = 0 ∧
      u x₀ = c • lp.single ∞ 0 (1 : ℝ) ∧
      ∀ᶠ x in 𝓝 x₀,
        (u x) 0 ≠ 0 ∧ F x = weierstrassPolynomialAction m (a x, u x) := by
  let w₀ : WeierstrassFactors m := (0, c • lp.single ∞ 0 (1 : ℝ))
  let R : E × WeierstrassFactors m → WeierstrassFactors m :=
    fun z => weierstrassSplit m (weierstrassPolynomialAction m z.2 - F z.1)
  have hR : AnalyticAt ℝ R (x₀, w₀) := by
    have hA : AnalyticAt ℝ
        (fun z : E × WeierstrassFactors m => weierstrassPolynomialAction m z.2)
        (x₀, w₀) :=
      AnalyticAt.comp (x := (x₀, w₀))
        (f := fun z : E × WeierstrassFactors m => z.2)
        (g := weierstrassPolynomialAction m)
        (analyticAt_weierstrassPolynomialAction m w₀) analyticAt_snd
    have hB : AnalyticAt ℝ
        (fun z : E × WeierstrassFactors m => F z.1) (x₀, w₀) :=
      hF.comp (f := fun z : E × WeierstrassFactors m => z.1) analyticAt_fst
    exact ((weierstrassSplit m).analyticAt _).comp (hA.fun_sub hB)
  have hR₀ : R (x₀, w₀) = 0 := by
    simp [R, w₀, hF₀]
  have hRd : HasFDerivAt (fun w => R (x₀, w))
      ((weierstrassSplit m).toContinuousLinearMap.comp (weierstrassLinearization m c)) w₀ := by
    exact (weierstrassSplit m).hasFDerivAt.comp w₀
      ((hasFDerivAt_weierstrassPolynomialAction m c).sub_const (F x₀))
  have hi : ((fderiv ℝ R (x₀, w₀)).comp
      (ContinuousLinearMap.inr ℝ E (WeierstrassFactors m))).IsInvertible := by
    rw [← fderiv_snd_slice R (x₀, w₀) hR.differentiableAt, hRd.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv.comp
      (weierstrassLinearization_isInvertible m c hc)
  obtain ⟨w, hw, hw₀, hzero, _⟩ := exists_analytic_implicit R x₀ w₀ hR hR₀ hi
  have ha : AnalyticAt ℝ (fun x => (w x).1) x₀ := analyticAt_fst.comp hw
  have hu : AnalyticAt ℝ (fun x => (w x).2) x₀ := analyticAt_snd.comp hw
  have hu₀ : (w x₀).2 = c • lp.single ∞ 0 (1 : ℝ) := congrArg Prod.snd hw₀
  have hval : (w x₀).2 0 ≠ 0 := by simpa only [hu₀, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply_self, smul_eq_mul, mul_one] using hc
  have hev := ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) ∞ 0).continuous.continuousAt.comp
    hu.continuousAt).eventually_ne hval
  refine ⟨fun x => (w x).1, fun x => (w x).2, ha, hu, congrArg Prod.fst hw₀, hu₀, ?_⟩
  filter_upwards [hev, hzero] with x hx hz
  refine ⟨hx, ?_⟩
  have h : weierstrassPolynomialAction m (w x) - F x = 0 := by
    exact (weierstrassSplit m).injective (by simpa only [map_zero] using hz)
  exact (sub_eq_zero.mp h).symm

end PlanarNikodym
