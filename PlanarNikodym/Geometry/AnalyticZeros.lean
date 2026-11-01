import PlanarNikodym.Geometry.LocalCoordinates
import PlanarNikodym.Geometry.RankTransport
import PlanarNikodym.Core.Definitions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

theorem analytic_zeros_finite_interval (I : Interval) (f : ℝ → ℝ)
    (hf : AnalyticOnNhd ℝ f I.carrier) (hn : ∃ t ∈ I.carrier, f t ≠ 0) :
    {t | t ∈ I.carrier ∧ f t = 0}.Finite := by
  rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Icc with he | he
  · obtain ⟨t, ht, hn⟩ := hn
    exact (hn (he ht)).elim
  · have h := isCompact_Icc.finite_sdiff_of_mem_codiscreteWithin he
    convert h using 1
    ext t
    simp [Interval.carrier]

theorem analytic_zeros_null_interval (I : Interval) (f : ℝ → ℝ)
    (hf : AnalyticOnNhd ℝ f I.carrier) (hn : ∃ t ∈ I.carrier, f t ≠ 0) :
    volume {t | t ∈ I.carrier ∧ f t = 0} = 0 :=
  (analytic_zeros_finite_interval I f hf hn).countable.measure_zero volume

def partialTime (h : Plane → ℝ) (p : Plane) : ℝ := fderiv ℝ h p (1, 0)
def partialParameter (h : Plane → ℝ) (p : Plane) : ℝ := fderiv ℝ h p (0, 1)

theorem partialTime_eq_deriv (h : Plane → ℝ) (p : Plane) (hf : DifferentiableAt ℝ h p) :
    partialTime h p = deriv (fun t => h (t, p.2)) p.1 := by
  change _ = fderiv ℝ (fun t => h (t, p.2)) p.1 1
  rw [fderiv_fst_slice h p hf]
  rfl

theorem partialParameter_eq_deriv (h : Plane → ℝ) (p : Plane) (hf : DifferentiableAt ℝ h p) :
    partialParameter h p = deriv (fun s => h (p.1, s)) p.2 := by
  change _ = fderiv ℝ (fun s => h (p.1, s)) p.2 1
  rw [fderiv_snd_slice h p hf]
  rfl

theorem analyticAt_partialTime {h : Plane → ℝ} {p : Plane} (hf : AnalyticAt ℝ h p) :
    AnalyticAt ℝ (partialTime h) p := by
  exact ((ContinuousLinearMap.apply ℝ ℝ ((1, 0) : Plane)).analyticAt _).comp hf.fderiv

theorem analyticAt_partialParameter {h : Plane → ℝ} {p : Plane} (hf : AnalyticAt ℝ h p) :
    AnalyticAt ℝ (partialParameter h) p := by
  exact ((ContinuousLinearMap.apply ℝ ℝ ((0, 1) : Plane)).analyticAt _).comp hf.fderiv

end PlanarNikodym
