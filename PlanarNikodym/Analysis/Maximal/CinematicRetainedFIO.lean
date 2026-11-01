import PlanarNikodym.Analysis.Maximal.CinematicPlaneFIO
import PlanarNikodym.Analysis.Maximal.RetainedFIOL2
import PlanarNikodym.Geometry.ParameterLebesgueCoordinates

/-! The full local cinematic FIO estimate in the original parameter measure.
The two selected axes and their actual complement form a volume-preserving
coordinate system; no retained parameter is discarded from the output norm. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

def cinematicRetainedCoordinates {d : ℕ} (σ : Fin 2 ↪ Fin (d+2)) :
    (UnselectedCoordinates σ × Plane) ≃L[ℝ] Parameters 2 d :=
  (ContinuousLinearEquiv.prodComm ℝ _ _).trans
    ((planeAuxEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ _)).trans
      ((selectedCoordinateSplit σ).trans (parameterFrame d)))

theorem cinematicRetainedCoordinates_volume_preserving {d : ℕ}
    (σ : Fin 2 ↪ Fin (d+2)) :
    MeasurePreserving (cinematicRetainedCoordinates σ) volume volume := by
  exact (parameterFrame_volume_preserving d).comp
    ((selectedCoordinateSplit_volume_preserving σ).comp
      ((planeAuxEquiv_measurePreserving.prod (MeasurePreserving.id volume)).comp
        Measure.measurePreserving_swap))

def Family.retainedCinematicPhase {d : ℕ} (G : Family 2 d)
    (σ : Fin 2 ↪ Fin (d+2)) (z : (UnselectedCoordinates σ × Plane) × Plane) : ℝ :=
  z.2.2 * G.γ z.2.1 (cinematicRetainedCoordinates σ z.1)

theorem Family.retainedCinematicPhase_contDiff {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (σ : Fin 2 ↪ Fin (d+2)) : ContDiff ℝ ∞ (G.retainedCinematicPhase σ) :=
  contDiff_snd.snd.mul (hG.comp (contDiff_snd.fst.prodMk
    ((cinematicRetainedCoordinates σ).contDiff.comp contDiff_fst)))

theorem Family.retainedCinematicPhase_gradient {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (σ : Fin 2 ↪ Fin (d+2)) (v : UnselectedCoordinates σ) (q x : Plane) :
    e2FIOParameterGradient e2FIOPlaneDirections
      (fun z : Plane × Plane => G.retainedCinematicPhase σ ((v,z.1),z.2)) (q,x) =
        G.e2SelectedPhaseGradient σ (cinematicRetainedCoordinates σ (v,q),x) := by
  have he : (fun z : Plane × Plane => G.retainedCinematicPhase σ ((v,z.1),z.2)) =
      G.selectedPlanePhase σ (selectedCoordinateSplit σ (0,v)) := by
    funext z
    unfold Family.retainedCinematicPhase Family.selectedPlanePhase
      Family.e2SelectedTimeFrequencyPhase
    congr 2
    exact congrArg (parameterFrame d) (selectedCoordinateSplit_eq_insertion σ _ _)
  rw [he,G.selectedPlanePhase_gradient hG]
  congr 2
  exact congrArg (parameterFrame d) (selectedCoordinateSplit_eq_insertion σ _ _).symm

theorem Family.exists_local_cinematic_full_fio_L2_bound {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (q₀ : Parameters 2 d) (x₀ : Plane) (hη : x₀.2 ≠ 0)
    (hd : G.cinematicDet (x₀.1,q₀) ≠ 0) :
    ∃ U : Set (Parameters 2 d × Plane), IsOpen U ∧ (q₀,x₀) ∈ U ∧
      ∀ a : Parameters 2 d × Plane → ℂ, ContDiff ℝ ∞ a → HasCompactSupport a →
        tsupport a ⊆ U → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        ∀ r : ℝ, 0 < r → ∀ f : Plane → ℂ, Continuous f →
          eLpNorm (e2FullFIOIntegral r (fun q x => x.2 * G.γ x.1 q) a f) 2 volume ≤
            C * ENNReal.ofReal r⁻¹ * eLpNorm f 2 volume := by
  obtain ⟨σ,U,c,hU,hx,hc,hs⟩ := G.exists_e2_cinematic_gradient_separation hG q₀ x₀ hη hd
  refine ⟨U,hU,hx,?_⟩
  intro a ha hac has
  let e := cinematicRetainedCoordinates σ
  let E := e.prodCongr (ContinuousLinearEquiv.refl ℝ Plane)
  have hE (z : (UnselectedCoordinates σ × Plane) × Plane) : E z = (e z.1,z.2) := rfl
  have hΦ := G.retainedCinematicPhase_contDiff hG σ
  have hO : IsOpen (E ⁻¹' U) := hU.preimage E.continuous
  have hsep : ∀ (v : UnselectedCoordinates σ) (q x y : Plane),
      ((v,q),x) ∈ E ⁻¹' U → ((v,q),y) ∈ E ⁻¹' U →
      c * ‖x-y‖ ≤ ‖e2FIOParameterGradient e2FIOPlaneDirections
        (fun z : Plane × Plane => G.retainedCinematicPhase σ ((v,z.1),z.2)) (q,x) -
        e2FIOParameterGradient e2FIOPlaneDirections
        (fun z : Plane × Plane => G.retainedCinematicPhase σ ((v,z.1),z.2)) (q,y)‖ := by
    intro v q x y hx hy
    rw [G.retainedCinematicPhase_gradient hG,G.retainedCinematicPhase_gradient hG]
    exact hs (e (v,q)) x y hx hy
  obtain ⟨C,hC,hbound⟩ := exists_retained_full_fio_L2_bound hΦ (ha.comp E.contDiff)
    (hac.comp_homeomorph E.toHomeomorph) hO hc hsep
    ((tsupport_comp_subset_preimage a E.continuous).trans (preimage_mono has))
  refine ⟨C,hC,?_⟩
  intro r hr f hf
  have hb := hbound r hr f hf
  have hK : Continuous (fun z : Parameters 2 d × Plane =>
      e2FIOAmplitudeKernel r (fun q x => x.2 * G.γ x.1 q) a z.1 z.2 * f z.2) := by
    unfold e2FIOAmplitudeKernel
    exact ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_snd.snd.mul (hG.continuous.comp
        (continuous_snd.fst.prodMk continuous_fst))))).mul continuous_const)).mul
          ha.continuous).mul (hf.comp continuous_snd)
  have hm : StronglyMeasurable
      (e2FullFIOIntegral r (fun q x => x.2 * G.γ x.1 q) a f) :=
    hK.stronglyMeasurable.integral_prod_right'
  have hnorm := eLpNorm_comp_measurePreserving hm.aestronglyMeasurable
    (cinematicRetainedCoordinates_volume_preserving σ) (p := (2 : ℝ≥0∞))
  change eLpNorm ((e2FullFIOIntegral r (fun q x => x.2 * G.γ x.1 q) a f) ∘ e)
    2 volume = _ at hnorm
  rw [← hnorm]
  exact hb

end PlanarNikodym
