import PlanarNikodym.Analysis.Fourier.WeightedPartialPlancherel
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! The actual nonlinear input coordinates for the degree-one cone phase.
The frequency map is `(τ,η) ↦ (η,ητ)`. Its Jacobian is retained in the
new input, and smooth compact data separated from `η=0` produces genuine
smooth compact data in these coordinates. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

def coneFrequencyMap (x : Plane) : Plane := (x.2, x.2 * x.1)
def coneFrequencyInverse (ξ : Plane) : Plane := (ξ.2 / ξ.1, ξ.1)
def coneFrequencyData (h : Plane → ℂ) (ξ : Plane) : ℂ :=
  |ξ.1|⁻¹ • h (coneFrequencyInverse ξ)

theorem continuous_coneFrequencyMap : Continuous coneFrequencyMap := by
  unfold coneFrequencyMap
  fun_prop

theorem coneFrequencyInverse_map {x : Plane} (hx : x.2 ≠ 0) :
    coneFrequencyInverse (coneFrequencyMap x) = x := by
  apply Prod.ext
  · exact mul_div_cancel_left₀ x.1 hx
  · rfl

theorem coneFrequencyMap_inverse {ξ : Plane} (hξ : ξ.1 ≠ 0) :
    coneFrequencyMap (coneFrequencyInverse ξ) = ξ := by
  apply Prod.ext
  · rfl
  · change ξ.1 * (ξ.2 / ξ.1) = ξ.2
    exact mul_div_cancel₀ ξ.2 hξ

/-- The image of the original compact support contains the support of
the actual Jacobian-weighted input. -/
theorem hasCompactSupport_coneFrequencyData {h : Plane → ℂ}
    (hc : HasCompactSupport h) : HasCompactSupport (coneFrequencyData h) := by
  apply HasCompactSupport.intro (hc.isCompact.image continuous_coneFrequencyMap)
  intro ξ hξ
  by_cases hzero : ξ.1 = 0
  · simp [coneFrequencyData, hzero]
  · have hh : h (coneFrequencyInverse ξ) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hi =>
        hξ ⟨coneFrequencyInverse ξ, hi, coneFrequencyMap_inverse hzero⟩)
    simp [coneFrequencyData, hh]

/-- Away from the cone vertex this is a smooth coordinate substitution. -/
theorem contDiffAt_coneFrequencyData {h : Plane → ℂ}
    (hh : ContDiff ℝ ∞ h) {ξ : Plane} (hξ : ξ.1 ≠ 0) :
    ContDiffAt ℝ ∞ (coneFrequencyData h) ξ := by
  have hi : ContDiffAt ℝ ∞ coneFrequencyInverse ξ :=
    ((contDiffAt_snd.div contDiffAt_fst hξ).prodMk contDiffAt_fst)
  exact ((contDiffAt_fst.abs hξ).inv (abs_ne_zero.mpr hξ)).smul
    (hh.contDiffAt.comp ξ hi)

/-- A genuine frequency gap removes the apparent singularity at the
vertex; no smoothness of division at zero is assumed. -/
theorem contDiff_coneFrequencyData {h : Plane → ℂ}
    (hh : ContDiff ℝ ∞ h) {a : ℝ} (ha : 0 < a)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    ContDiff ℝ ∞ (coneFrequencyData h) := by
  apply contDiff_iff_contDiffAt.mpr
  intro ξ
  by_cases hξ : ξ.1 = 0
  · have hU : {y : Plane | |y.1| < a} ∈ nhds ξ :=
      (isOpen_lt continuous_fst.abs continuous_const).mem_nhds (by simpa [hξ] using ha)
    have he : coneFrequencyData h =ᶠ[nhds ξ] fun _ => (0 : ℂ) := by
      filter_upwards [hU] with y hy
      simp [coneFrequencyData, hgap (coneFrequencyInverse y) hy]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact contDiffAt_coneFrequencyData hh hξ

/-- The frequency-coordinate input is an actual Schwartz function. -/
def coneFrequencySchwartz (h : Plane → ℂ) (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) {a : ℝ} (ha : 0 < a)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) : SchwartzMap Plane ℂ :=
  (hasCompactSupport_coneFrequencyData hc).toSchwartzMap
    (contDiff_coneFrequencyData hh ha hgap)

@[simp] theorem coneFrequencySchwartz_apply (h : Plane → ℂ) (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) {a : ℝ} (ha : 0 < a)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) (ξ : Plane) :
    coneFrequencySchwartz h hh hc ha hgap ξ = coneFrequencyData h ξ := rfl

end PlanarNikodym
