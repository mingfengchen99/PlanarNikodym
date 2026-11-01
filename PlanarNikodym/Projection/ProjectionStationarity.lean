import PlanarNikodym.Projection.ScalarProjectionGeometry
import Mathlib.Analysis.Calculus.MeanValue

/-! An elementary stationary-branch reduction from §7.3, Step 4.

On a patch where the first gradient component is nonzero, projective
stationarity is expressed by constancy of the ratio of the two components.
The normalization on the base slice then forces independence of the second
parameter. All derivatives below are derivatives of the given function.
No Nikodym construction is assumed or supplied in this file. -/

noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

def scalarHeadDerivative (ψ : ℝ × Plane → ℝ) (p : ℝ × Plane) : ℝ :=
  fderiv ℝ ψ p (0, (1, 0))

def scalarTailDerivative (ψ : ℝ × Plane → ℝ) (p : ℝ × Plane) : ℝ :=
  fderiv ℝ ψ p (0, (0, 1))

/-- A coordinate for the projective direction of the parameter gradient,
valid where `scalarHeadDerivative` is nonzero. -/
def scalarGradientSlope (ψ : ℝ × Plane → ℝ) (p : ℝ × Plane) : ℝ :=
  scalarTailDerivative ψ p / scalarHeadDerivative ψ p

theorem scalarHeadDerivative_analyticAt {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hψ : AnalyticAt ℝ ψ p) : AnalyticAt ℝ (scalarHeadDerivative ψ) p :=
  ((ContinuousLinearMap.apply ℝ ℝ ((0, (1, 0)) : ℝ × Plane)).analyticAt _).comp hψ.fderiv

theorem scalarTailDerivative_analyticAt {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hψ : AnalyticAt ℝ ψ p) : AnalyticAt ℝ (scalarTailDerivative ψ) p :=
  ((ContinuousLinearMap.apply ℝ ℝ ((0, (0, 1)) : ℝ × Plane)).analyticAt _).comp hψ.fderiv

theorem scalarGradientSlope_analyticAt {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hψ : AnalyticAt ℝ ψ p) (hh : scalarHeadDerivative ψ p ≠ 0) :
    AnalyticAt ℝ (scalarGradientSlope ψ) p :=
  (scalarTailDerivative_analyticAt hψ).div (scalarHeadDerivative_analyticAt hψ) hh

/-- The normalized base slice has the genuine parameter gradient `(1,0)`. -/
theorem scalar_parameter_derivatives_of_normalize
    {ψ : ℝ × Plane → ℝ} {Y S : Set ℝ} (hY : IsOpen Y) (hS : IsOpen S)
    (b : ℝ) (q : Plane) (hq : q ∈ Y ×ˢ S)
    (hψ : DifferentiableAt ℝ ψ (b, q))
    (hn : ∀ q ∈ Y ×ˢ S, ψ (b, q) = q.1) :
    scalarHeadDerivative ψ (b, q) = 1 ∧ scalarTailDerivative ψ (b, q) = 0 := by
  have he : (fun q : Plane => ψ (b, q)) =ᶠ[𝓝 q] Prod.fst := by
    filter_upwards [(hY.prod hS).mem_nhds hq] with p hp
    exact hn p hp
  have hd : (fderiv ℝ ψ (b, q)).comp (ContinuousLinearMap.inr ℝ ℝ Plane) =
      ContinuousLinearMap.fst ℝ ℝ ℝ := by
    rw [← fderiv_snd_slice ψ (b, q) hψ, he.fderiv_eq]
    exact (ContinuousLinearMap.fst ℝ ℝ ℝ).fderiv
  constructor
  · exact congrArg (fun L : Plane →L[ℝ] ℝ => L (1, 0)) hd
  · exact congrArg (fun L : Plane →L[ℝ] ℝ => L (0, 1)) hd

/-- On an open connected interval of the first variable, a stationary
projective slope and the normalized base slice force the second parameter
derivative to vanish everywhere. -/
theorem scalarTailDerivative_eq_zero_of_stationary
    {ψ : ℝ × Plane → ℝ} {X Y S : Set ℝ}
    (hX : IsOpen X) (hXc : IsPreconnected X) (hY : IsOpen Y) (hS : IsOpen S)
    (b : ℝ) (hb : b ∈ X)
    (hψ : AnalyticOnNhd ℝ ψ (X ×ˢ (Y ×ˢ S)))
    (hn : ∀ q ∈ Y ×ˢ S, ψ (b, q) = q.1)
    (hh : ∀ p ∈ X ×ˢ (Y ×ˢ S), scalarHeadDerivative ψ p ≠ 0)
    (hst : ∀ q ∈ Y ×ˢ S, ∀ x ∈ X,
      deriv (fun a => scalarGradientSlope ψ (a, q)) x = 0)
    (x : ℝ) (hx : x ∈ X) (q : Plane) (hq : q ∈ Y ×ˢ S) :
    scalarTailDerivative ψ (x, q) = 0 := by
  have hd : DifferentiableOn ℝ (fun a => scalarGradientSlope ψ (a, q)) X := by
    intro a ha
    exact ((scalarGradientSlope_analyticAt (hψ (a, q) ⟨ha, hq⟩)
      (hh (a, q) ⟨ha, hq⟩)).comp
        (f := fun a : ℝ => (a, q)) (analyticAt_id.prod analyticAt_const)).differentiableAt.differentiableWithinAt
  have hslope : scalarGradientSlope ψ (x, q) = scalarGradientSlope ψ (b, q) :=
    hX.is_const_of_deriv_eq_zero hXc hd (fun a ha => hst q hq a ha) hx hb
  have hn' := scalar_parameter_derivatives_of_normalize hY hS b q hq
    (hψ (b, q) ⟨hb, hq⟩).differentiableAt hn
  have hz : scalarGradientSlope ψ (b, q) = 0 := by
    simp only [scalarGradientSlope, hn'.1, hn'.2, zero_div]
  have hratio : scalarTailDerivative ψ (x, q) / scalarHeadDerivative ψ (x, q) = 0 :=
    hslope.trans hz
  exact (div_eq_zero_iff).mp hratio |>.resolve_right (hh (x, q) ⟨hx, hq⟩)

/-- The stationary branch factors through the first parameter: after
normalization, `ψ (x,(y,s))` is independent of `s` on the connected patch.
This is the differential content of §7.3, Step 4. -/
theorem scalar_stationary_independent_tail
    {ψ : ℝ × Plane → ℝ} {X Y S : Set ℝ}
    (hX : IsOpen X) (hXc : IsPreconnected X) (hY : IsOpen Y)
    (hS : IsOpen S) (hSc : IsPreconnected S)
    (b : ℝ) (hb : b ∈ X)
    (hψ : AnalyticOnNhd ℝ ψ (X ×ˢ (Y ×ˢ S)))
    (hn : ∀ q ∈ Y ×ˢ S, ψ (b, q) = q.1)
    (hh : ∀ p ∈ X ×ˢ (Y ×ˢ S), scalarHeadDerivative ψ p ≠ 0)
    (hst : ∀ q ∈ Y ×ˢ S, ∀ x ∈ X,
      deriv (fun a => scalarGradientSlope ψ (a, q)) x = 0)
    (x : ℝ) (hx : x ∈ X) (y : ℝ) (hy : y ∈ Y)
    (s s₀ : ℝ) (hs : s ∈ S) (hs₀ : s₀ ∈ S) :
    ψ (x, (y, s)) = ψ (x, (y, s₀)) := by
  have hd (a : ℝ) (ha : a ∈ S) : HasDerivAt (fun a => ψ (x, (y, a)))
      (scalarTailDerivative ψ (x, (y, a))) a := by
    apply (hψ (x, (y, a)) ⟨hx, hy, ha⟩).differentiableAt.hasFDerivAt.comp_hasDerivAt
    exact (hasDerivAt_const a x).prodMk
      ((hasDerivAt_const a y).prodMk (hasDerivAt_id a))
  apply hS.is_const_of_deriv_eq_zero hSc
    (fun a ha => (hd a ha).differentiableAt.differentiableWithinAt)
    (fun a ha => ?_) hs hs₀
  rw [(hd a ha).deriv]
  exact scalarTailDerivative_eq_zero_of_stationary hX hXc hY hS b hb hψ hn hh hst
    x hx (y, a) ⟨hy, ha⟩

end PlanarNikodym
