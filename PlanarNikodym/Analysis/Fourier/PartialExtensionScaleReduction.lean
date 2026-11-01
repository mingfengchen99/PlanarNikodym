import PlanarNikodym.Analysis.Fourier.UniformLowerDegreeReduction
import PlanarNikodym.Analysis.Fourier.LocalAmplitudeExtension
import PlanarNikodym.Analysis.Fourier.ExtensionBoxLocalization
import PlanarNikodym.Analysis.Fourier.TimeDataScaling
import PlanarNikodym.Analysis.Fourier.CriticalScaleThreshold
import PlanarNikodym.Analysis.Fourier.PartialExtensionLocalization
import PlanarNikodym.Analysis.Fourier.PartialExtensionMeasurability
import PlanarNikodym.Geometry.ParameterLebesgueCoordinates
import PlanarNikodym.Analysis.Localization.MovingChartPartition
import PlanarNikodym.Analysis.Localization.BoxOverlapIntegral

/-! A4.2: the actual partial-Fourier main term, including its `r²`
prefactor and Fourier normalization, has the constructed lower-degree
extension norm reduction. The decoupling estimate for that extension
is the separate A4.3 task. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem Family.cutoffPartialExtension_lowerDegree_Lp_reduction {d n : ℕ} (G : Family 2 d)
    (hm : n + 1 ≤ d + 2) (σ : Fin (n + 1) ↪ Fin (d + 2))
    (v : Aux (d + 2)) (c : ℝ) (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : ∀ z, e z = G.lowerCinematicJetMap hm σ c v z)
    (hea : AnalyticOnNhd ℝ e e.source)
    (ha : ∀ z ∈ e.source, AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (c, parameterFrame d (v + coordinateInsertion σ z)))
    {K : Set (Aux (n + 1))} (hK : MeasurableSet K) (hKS : K ⊆ e.source)
    {b : ℝ} (hb : 0 ≤ b)
    (hJ : ∀ z ∈ K, b ≤ |LinearMap.det (fderiv ℝ e z).toLinearMap|)
    (χ : Cutoff d) (L : FrequencyCutoff) (β : ℝ → ℝ) (f : Plane → ℂ)
    (r : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : ℝ≥0∞) (hp : p ≠ 0) (hpt : p ≠ ∞) :
    ENNReal.ofReal (b * |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n|) ^ (1 / p.toReal) *
      eLpNorm (fun z => G.cutoffPartialExtension
        (fun x => χ x * timePartitionWindow ((x.1 - c) / δ)) L β r f
        (parameterFrame d (v + coordinateInsertion σ z))) p (volume.restrict K) ≤
      ENNReal.ofReal (r ^ 2 * δ) * eLpNorm
        (G.lowerChartExtension σ v e (fun x => (χ (x.2.1, x.1) : ℂ))
          (fun x => weightedPartialFourierData (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2)
            f r x.1 x.2) (2 * Real.pi * r) c δ hδ.ne') p
        (volume.restrict (lowerDegreeDilation n δ hδ.ne' '' (e '' K))) := by
  let a : Parameters 2 d × ℝ × ℝ → ℂ := fun x => (χ (x.2.1, x.1) : ℂ)
  let h : ℝ × ℝ → ℂ := fun x => weightedPartialFourierData
    (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) f r x.1 x.2
  let T := fun z => timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
    a h (2 * Real.pi * r) c δ (parameterFrame d (v + coordinateInsertion σ z))
  let E := G.lowerChartExtension σ v e a h (2 * Real.pi * r) c δ hδ.ne'
  let C := ENNReal.ofReal (b * |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n|) ^ (1 / p.toReal)
  have hOp : (fun z => G.cutoffPartialExtension
      (fun x => χ x * timePartitionWindow ((x.1 - c) / δ)) L β r f
      (parameterFrame d (v + coordinateInsertion σ z))) = r ^ 2 • T := by
    funext z
    exact G.cutoffPartialExtension_timeSlice χ L β r c δ f _
  rw [hOp, eLpNorm_const_smul]
  have hred : C * eLpNorm T p (volume.restrict K) ≤
      ENNReal.ofReal δ * eLpNorm E p
        (volume.restrict (lowerDegreeDilation n δ hδ.ne' '' (e '' K))) :=
    G.timeSliceExtension_lowerDegree_Lp_reduction hm σ v c e he hea ha hK hKS hb hJ a h
      (2 * Real.pi * r) hδ p hp hpt
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg r)]
  change C * (ENNReal.ofReal (r ^ 2) * eLpNorm T p (volume.restrict K)) ≤ _
  calc
    _ = ENNReal.ofReal (r ^ 2) * (C * eLpNorm T p (volume.restrict K)) := by ac_rfl
    _ ≤ ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal δ * eLpNorm E p
        (volume.restrict (lowerDegreeDilation n δ hδ.ne' '' (e '' K)))) := mul_le_mul_right hred _
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg r)]

end PlanarNikodym
