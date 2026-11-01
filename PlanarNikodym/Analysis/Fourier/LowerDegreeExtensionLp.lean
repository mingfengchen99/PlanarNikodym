import PlanarNikodym.Analysis.Fourier.TimeSliceExtension
import PlanarNikodym.Analysis.Fourier.ScaledChartLp
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! An actual extension norm reduction, not a hypothesis asserting an
extension bound. The operator on the right is explicitly constructed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

def Family.lowerChartExtension {d n : ℕ} (G : Family 2 d)
    (σ : Fin (n + 1) ↪ Fin (d + 2)) (v : Aux (d + 2))
    (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (a : Parameters 2 d × ℝ × ℝ → ℂ) (h : ℝ × ℝ → ℂ)
    (r c δ : ℝ) (hδ : δ ≠ 0) : Aux (n + 1) → ℂ :=
  polynomialExtension
    (fun w τ η => actualTaylorAmplitude a (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
      n r c δ (parameterFrame d (v + coordinateInsertion σ
        (e.symm ((lowerDegreeDilation n δ hδ).symm w)))) τ η)
    (fun x => h (c + δ * x.1, x.2)) (r * δ ^ n)

theorem Family.timeSliceExtension_lowerDegree_Lp_reduction {d n : ℕ} (G : Family 2 d)
    (hm : n + 1 ≤ d + 2) (σ : Fin (n + 1) ↪ Fin (d + 2))
    (v : Aux (d + 2)) (c : ℝ) (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : ∀ z, e z = G.lowerCinematicJetMap hm σ c v z)
    (hea : AnalyticOnNhd ℝ e e.source)
    (ha : ∀ z ∈ e.source, AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (c, parameterFrame d (v + coordinateInsertion σ z)))
    {K : Set (Aux (n + 1))} (hK : MeasurableSet K) (hKS : K ⊆ e.source)
    {b : ℝ} (hb : 0 ≤ b)
    (hJ : ∀ z ∈ K, b ≤ |LinearMap.det (fderiv ℝ e z).toLinearMap|)
    (a : Parameters 2 d × ℝ × ℝ → ℂ) (h : ℝ × ℝ → ℂ)
    (r : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : ℝ≥0∞) (hp : p ≠ 0) (hpt : p ≠ ∞) :
    ENNReal.ofReal (b * |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n|) ^ (1 / p.toReal) *
      eLpNorm (fun z => timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
        a h r c δ (parameterFrame d (v + coordinateInsertion σ z))) p (volume.restrict K) ≤
      ENNReal.ofReal δ * eLpNorm (G.lowerChartExtension σ v e a h r c δ hδ.ne') p
        (volume.restrict (lowerDegreeDilation n δ hδ.ne' '' (e '' K))) := by
  let E := G.lowerChartExtension σ v e a h r c δ hδ.ne'
  have heq : (fun z => timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
      a h r c δ (parameterFrame d (v + coordinateInsertion σ z))) =ᵐ[volume.restrict K]
      fun z => δ • E (lowerDegreeDilation n δ hδ.ne' (e z)) := by
    filter_upwards [ae_restrict_mem hK] with z hz
    have hw : lowerDegreeDilation n δ hδ.ne' (e z) ∈
        lowerDegreeDilation n δ hδ.ne' '' e.target :=
      mem_image_of_mem _ (e.map_source (hKS hz))
    have hred := G.timeSliceExtension_in_scaled_lower_chart hm σ v c e he ha a h r hδ hw
    simpa only [E, Family.lowerChartExtension, ContinuousLinearEquiv.symm_apply_apply,
      e.left_inv (hKS hz)] using hred
  rw [eLpNorm_congr_ae heq]
  have htrans := scaled_chart_eLpNorm_lower_bound e hea hK hKS hb hJ δ hδ.ne'
    (fun w => δ • E w) p hp hpt
  have hnorm : eLpNorm (fun w => δ • E w) p
      (volume.restrict (lowerDegreeDilation n δ hδ.ne' '' (e '' K))) =
      ENNReal.ofReal δ * eLpNorm E p
        (volume.restrict (lowerDegreeDilation n δ hδ.ne' '' (e '' K))) := by
    rw [show (fun w => δ • E w) = δ • E from rfl, eLpNorm_const_smul]
    congr 1
    simp [Real.enorm_eq_ofReal_abs, abs_of_pos hδ]
  exact htrans.trans_eq hnorm

end PlanarNikodym
