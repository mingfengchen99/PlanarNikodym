import PlanarNikodym.Analysis.Fourier.FrozenAmplitudeFamily
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Integrating an actual compact smooth kernel against an L¹ input
produces a compact smooth function. In particular, localization of an
oscillatory extension is genuinely Schwartz even for nonsmooth inputs. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace PlanarNikodym

variable {X Y F : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

def compactKernelFiberDeriv (H : X × Y → F) (q : X × Y) : X →L[ℝ] F :=
  fderiv ℝ (fun x => H (x, q.2)) q.1

omit [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
theorem contDiff_compactKernelFiberDeriv {H : X × Y → F}
    (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (compactKernelFiberDeriv H) :=
  contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_fiber_fderiv hH.contDiffAt

omit [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
theorem hasCompactSupport_compactKernelFiberDeriv {H : X × Y → F}
    (hc : HasCompactSupport H) : HasCompactSupport (compactKernelFiberDeriv H) := by
  apply HasCompactSupport.intro hc.isCompact
  intro q hq
  have hz : (fun x => H (x, q.2)) =ᶠ[𝓝 q.1] 0 :=
    (notMem_tsupport_iff_eventuallyEq.mp hq).comp_tendsto
      (continuous_id.prodMk continuous_const).continuousAt
  simpa only [compactKernelFiberDeriv, Pi.zero_def, fderiv_fun_const] using hz.fderiv_eq

omit [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
theorem integrable_compactKernel_smul (μ : Measure Y) {g : Y → ℂ}
    (hg : Integrable g μ) {H : X × Y → F}
    (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) (x : X) :
    Integrable (fun y => g y • H (x, y)) μ := by
  let S : SchwartzMap (X × Y) F := hc.toSchwartzMap hH
  have hm : AEStronglyMeasurable (fun y => g y • H (x, y)) μ :=
    hg.aestronglyMeasurable.smul
      ((hH.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  apply (hg.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 S)).mono' hm
  filter_upwards [] with y
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (S.norm_le_seminorm ℝ (x, y)) (norm_nonneg _)

omit [CompleteSpace F] in
theorem hasFDerivAt_integral_compactKernel_smul (μ : Measure Y) {g : Y → ℂ}
    (hg : Integrable g μ) {H : X × Y → F}
    (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) (x : X) :
    HasFDerivAt (fun z => ∫ y, g y • H (z, y) ∂μ)
      (∫ y, g y • compactKernelFiberDeriv H (x, y) ∂μ) x := by
  let D := compactKernelFiberDeriv H
  have hD : ContDiff ℝ ∞ D := contDiff_compactKernelFiberDeriv hH
  have hDc : HasCompactSupport D := hasCompactSupport_compactKernelFiberDeriv hc
  let S : SchwartzMap (X × Y) (X →L[ℝ] F) := hDc.toSchwartzMap hD
  let C := SchwartzMap.seminorm ℝ 0 0 S
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun z y => g y • D (z, y)) (s := univ)
    (bound := fun y => ‖g y‖ * C) Filter.univ_mem
    (Eventually.of_forall fun z => (integrable_compactKernel_smul μ hg hH hc z).aestronglyMeasurable)
    (integrable_compactKernel_smul μ hg hH hc x)
    (integrable_compactKernel_smul μ hg hD hDc x).aestronglyMeasurable
  · filter_upwards [] with y z _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (S.norm_le_seminorm ℝ (z, y)) (norm_nonneg _)
  · exact hg.norm.mul_const C
  · filter_upwards [] with y z _
    exact (((hH.comp (contDiff_id.prodMk (contDiff_const (c := y)))).differentiable
      (by norm_num)) z).hasFDerivAt.const_smul (g y)

theorem contDiff_nat_integral_compactKernel_smul (n : ℕ) (μ : Measure Y)
    {g : Y → ℂ} (hg : Integrable g μ) {H : X × Y → F}
    (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) :
    ContDiff ℝ n (fun z => ∫ y, g y • H (z, y) ∂μ) := by
  induction n generalizing F with
  | zero =>
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun x =>
      (hasFDerivAt_integral_compactKernel_smul μ hg hH hc x).continuousAt)
  | succ n ih =>
    exact contDiff_succ_iff_hasFDerivAt.mpr
      ⟨fun z => ∫ y, g y • compactKernelFiberDeriv H (z, y) ∂μ,
        ih (contDiff_compactKernelFiberDeriv hH) (hasCompactSupport_compactKernelFiberDeriv hc),
        hasFDerivAt_integral_compactKernel_smul μ hg hH hc⟩

theorem contDiff_integral_compactKernel_smul (μ : Measure Y)
    {g : Y → ℂ} (hg : Integrable g μ) {H : X × Y → F}
    (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) :
    ContDiff ℝ ∞ (fun z => ∫ y, g y • H (z, y) ∂μ) :=
  contDiff_infty.mpr fun n => contDiff_nat_integral_compactKernel_smul n μ hg hH hc

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] [BorelSpace Y] [SecondCountableTopology Y]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
theorem hasCompactSupport_integral_compactKernel_smul (μ : Measure Y)
    (g : Y → ℂ) {H : X × Y → F} (hc : HasCompactSupport H) :
    HasCompactSupport (fun z => ∫ y, g y • H (z, y) ∂μ) := by
  apply HasCompactSupport.intro (hc.isCompact.image continuous_fst)
  intro x hx
  have hz (y : Y) : H (x, y) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hx ⟨(x, y), h, rfl⟩
  simp only [hz, smul_zero, integral_zero]

def compactKernelIntegralSchwartz (μ : Measure Y) (g : Y → ℂ)
    (hg : Integrable g μ) (H : X × Y → F)
    (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) : SchwartzMap X F :=
  (hasCompactSupport_integral_compactKernel_smul μ g hc).toSchwartzMap
    (contDiff_integral_compactKernel_smul μ hg hH hc)

@[simp] theorem compactKernelIntegralSchwartz_apply (μ : Measure Y) (g : Y → ℂ)
    (hg : Integrable g μ) (H : X × Y → F)
    (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) (x : X) :
    compactKernelIntegralSchwartz μ g hg H hH hc x = ∫ y, g y • H (x, y) ∂μ := rfl

end PlanarNikodym
