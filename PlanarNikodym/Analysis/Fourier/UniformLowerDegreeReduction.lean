import PlanarNikodym.Analysis.Fourier.LowerDegreeExtensionLp
import PlanarNikodym.Analysis.Fourier.MovingCinematicBounds
import PlanarNikodym.Analysis.Localization.CoefficientBoxPartition

/-! The cinematic assumptions construct a family of actual extension
norm reductions with one positive Jacobian constant for all frozen
parameters and time centers in the same compact joint chart. -/
noncomputable section
open Set
open scoped ENNReal Topology
namespace PlanarNikodym

theorem Family.exists_uniform_lowerDegree_extension_Lp_reduction {d n : ℕ}
    (G : Family 2 d) {t : ℝ} {v : Aux (d + 2)}
    (ha : AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (t, parameterFrame d v))
    (hdet : G.cinematicDet (t, parameterFrame d v) ≠ 0) (hm : n + 1 ≤ d + 2) :
    ∃ (σ : Fin (n + 1) ↪ Fin (d + 2))
      (K : Set ((ℝ × Aux (d + 2)) × Aux (n + 1))) (b : ℝ),
      IsCompact K ∧ ((t, v), (0 : Aux (n + 1))) ∈ interior K ∧ 0 < b ∧
      ∀ q : ℝ × Aux (d + 2),
        ∃ e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)),
          (∀ z, e z = G.lowerCinematicJetMap hm σ q.1 q.2 z) ∧
          {z | (q, z) ∈ K} ⊆ e.source ∧
          ∀ (a : Parameters 2 d × ℝ × ℝ → ℂ) (h : ℝ × ℝ → ℂ)
            (r δ : ℝ) (hδ : 0 < δ) (p : ℝ≥0∞), p ≠ 0 → p ≠ ∞ →
            ENNReal.ofReal (b * |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n|) ^ (1 / p.toReal) *
              MeasureTheory.eLpNorm (fun z => timeSliceExtension
                (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h r q.1 δ
                (parameterFrame d (q.2 + coordinateInsertion σ z))) p
                (MeasureTheory.volume.restrict {z | (q, z) ∈ K}) ≤
              ENNReal.ofReal δ * MeasureTheory.eLpNorm
                (G.lowerChartExtension σ q.2 e a h r q.1 δ hδ.ne') p
                (MeasureTheory.volume.restrict
                  (lowerDegreeDilation n δ hδ.ne' '' (e '' {z | (q, z) ∈ K}))) := by
  obtain ⟨σ, E, K, L, hK, _, hxK, hKS, _, _, he, hea, hei,
    ⟨b, C, hb, _, hJ⟩, _, hreg⟩ := G.exists_uniform_movingLowerJet_chart ha hdet (n + 1) hm
  have hfirst : ∀ x, (E x).1 = x.1 := by intro x; rw [he]
  refine ⟨σ, K, b, hK, hxK, hb, ?_⟩
  intro q
  let e := retainedParameterFiber E hfirst q
  have hef : ∀ z, e z = G.lowerCinematicJetMap hm σ q.1 q.2 z := by
    intro z
    change (E (q, z)).2 = _
    rw [he]
    rfl
  have hsub : {z | (q, z) ∈ K} ⊆ e.source := fun _ hz => hKS hz
  refine ⟨e, hef, hsub, ?_⟩
  intro a h r δ hδ p hp hpt
  have hmeas : MeasurableSet {z | (q, z) ∈ K} :=
    hK.isClosed.measurableSet.preimage (continuous_const.prodMk continuous_id).measurable
  exact G.timeSliceExtension_lowerDegree_Lp_reduction hm σ q.2 q.1 e hef
    (retainedParameterFiber_analytic hfirst hea hei q).1
    (fun z hz => hreg (q, z) hz) hmeas hsub hb.le
    (fun z hz => (hJ (q, z) hz).1) a h r hδ p hp hpt

end PlanarNikodym
