import PlanarNikodym.Analysis.Maximal.E2FIOCinematicGradient
import PlanarNikodym.Analysis.Maximal.E2FIOLocalEnergy

/-! The actual selected cinematic phase in product-plane coordinates.
The coordinate map preserves volume and its derivatives give exactly
the selected parameter columns. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace PlanarNikodym

def planeAuxEquiv : Plane ≃L[ℝ] Aux 2 :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm

@[simp] theorem planeAuxEquiv_zero : planeAuxEquiv 0 = 0 := map_zero _

@[simp] theorem planeAuxEquiv_direction (j : Fin 2) :
    planeAuxEquiv (e2FIOPlaneDirections j) = Pi.single j 1 := by
  funext i
  change (finTwoArrowEquiv ℝ).symm (e2FIOPlaneDirections j) i = (Pi.single j (1 : ℝ) : Aux 2) i
  fin_cases i <;> fin_cases j <;> simp [finTwoArrowEquiv, e2FIOPlaneDirections]

theorem planeAuxEquiv_measurePreserving :
    MeasurePreserving planeAuxEquiv volume volume := by
  exact (volume_preserving_finTwoArrow ℝ).symm

def Family.selectedPlanePhase {d : ℕ} (G : Family 2 d)
    (σ : Fin 2 ↪ Fin (d+2)) (v : Aux (d+2)) (z : Plane × Plane) : ℝ :=
  G.e2SelectedTimeFrequencyPhase σ v (planeAuxEquiv z.1) z.2

theorem Family.selectedPlanePhase_contDiff {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (σ : Fin 2 ↪ Fin (d+2)) (v : Aux (d+2)) :
    ContDiff ℝ ∞ (G.selectedPlanePhase σ v) :=
  (G.e2SelectedTimeFrequencyPhase_contDiff hG σ v).comp
    ((planeAuxEquiv.contDiff.comp contDiff_fst).prodMk contDiff_snd)

theorem Family.selectedPlanePhase_gradient {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (σ : Fin 2 ↪ Fin (d+2)) (v : Aux (d+2)) (q x : Plane) :
    e2FIOParameterGradient e2FIOPlaneDirections (G.selectedPlanePhase σ v) (q,x) =
      G.e2SelectedPhaseGradient σ
        (parameterFrame d (v + coordinateInsertion σ (planeAuxEquiv q)),x) := by
  have hdiff : Differentiable ℝ (fun u : Aux 2 => G.e2SelectedTimeFrequencyPhase σ v u x) :=
    ((G.e2SelectedTimeFrequencyPhase_contDiff hG σ v).comp
      (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp)
  have hder := hdiff.differentiableAt.hasFDerivAt.comp q planeAuxEquiv.hasFDerivAt
  have he (j : Fin 2) :
      fderiv ℝ (fun w : Plane => G.selectedPlanePhase σ v (w,x)) q
        (e2FIOPlaneDirections j) =
      x.2 * G.parameterColumn (σ j)
        (x.1,parameterFrame d (v + coordinateInsertion σ (planeAuxEquiv q))) := by
    change fderiv ℝ ((fun u : Aux 2 => G.e2SelectedTimeFrequencyPhase σ v u x) ∘ planeAuxEquiv)
      q _ = _
    rw [hder.fderiv, ContinuousLinearMap.comp_apply]
    change fderiv ℝ (fun u : Aux 2 => G.e2SelectedTimeFrequencyPhase σ v u x)
      (planeAuxEquiv q) (planeAuxEquiv (e2FIOPlaneDirections j)) = _
    rw [planeAuxEquiv_direction]
    exact G.e2SelectedTimeFrequencyPhase_fderiv_single hG σ v _ x j
  exact Prod.ext (he 0) (he 1)

def Family.selectedPlanePatch {d : ℕ} (_G : Family 2 d)
    (σ : Fin 2 ↪ Fin (d+2)) (v : Aux (d+2))
    (O : Set (Parameters 2 d × Plane)) : Set (Plane × Plane) :=
  (fun z : Plane × Plane =>
    (parameterFrame d (v + coordinateInsertion σ (planeAuxEquiv z.1)),z.2)) ⁻¹' O

theorem Family.exists_selectedPlane_phase_separation {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (q₀ : Parameters 2 d) (x₀ : Plane) (hη : x₀.2 ≠ 0)
    (hd : G.cinematicDet (x₀.1,q₀) ≠ 0) :
    ∃ (σ : Fin 2 ↪ Fin (d+2)) (O : Set (Plane × Plane)) (c : ℝ),
      IsOpen O ∧ (0,x₀) ∈ O ∧ 0 < c ∧
      ∀ (q x y : Plane), (q,x) ∈ O → (q,y) ∈ O →
        c * ‖x-y‖ ≤ ‖e2FIOParameterGradient e2FIOPlaneDirections
            (G.selectedPlanePhase σ ((parameterFrame d).symm q₀)) (q,x) -
          e2FIOParameterGradient e2FIOPlaneDirections
            (G.selectedPlanePhase σ ((parameterFrame d).symm q₀)) (q,y)‖ := by
  obtain ⟨σ,U,c,hU,hx,hc,hs⟩ := G.exists_e2_cinematic_gradient_separation hG q₀ x₀ hη hd
  let v := (parameterFrame d).symm q₀
  refine ⟨σ,G.selectedPlanePatch σ v U,c,?_,?_,hc,?_⟩
  · exact hU.preimage (((parameterFrame d).continuous.comp
      (continuous_const.add ((coordinateInsertion σ).continuous.comp
        (planeAuxEquiv.continuous.comp continuous_fst)))).prodMk continuous_snd)
  · simpa [Family.selectedPlanePatch,v] using hx
  · intro q x y hx hy
    rw [G.selectedPlanePhase_gradient hG,G.selectedPlanePhase_gradient hG]
    exact hs _ x y hx hy

end PlanarNikodym
