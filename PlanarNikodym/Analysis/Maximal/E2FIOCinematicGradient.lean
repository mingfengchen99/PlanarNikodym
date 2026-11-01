import PlanarNikodym.Analysis.Maximal.E2FIOGradientSeparation
import PlanarNikodym.Analysis.Maximal.E2FIOFullKernel
/-! The original cinematic determinant selects two genuine parameter directions.
The resulting derivatives of the full time/vertical-frequency phase separate
nearby input points uniformly in all retained parameters. The inverse linear
map, the minor calculation, and the retained inverse chart are constructed. -/
noncomputable section
open scoped ContDiff
open Function Set
set_option autoImplicit false
namespace PlanarNikodym
theorem e2_plane_two_by_two_isInvertible (a b c d : ℝ) (hd : a * d - b * c ≠ 0) :
    (((a • ContinuousLinearMap.fst ℝ ℝ ℝ) + b • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (c • ContinuousLinearMap.fst ℝ ℝ ℝ + d • ContinuousLinearMap.snd ℝ ℝ ℝ)).IsInvertible := by
  let L : Plane →L[ℝ] Plane :=
    (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (c • ContinuousLinearMap.fst ℝ ℝ ℝ + d • ContinuousLinearMap.snd ℝ ℝ ℝ)
  let M : Plane →L[ℝ] Plane :=
    ((d / (a * d - b * c)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (-b / (a * d - b * c)) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((-c / (a * d - b * c)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (a / (a * d - b * c)) • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hML : LeftInverse M L := by
    rintro ⟨x, y⟩
    apply Prod.ext
    · change (d / (a*d-b*c)) * (a*x+b*y) + (-b / (a*d-b*c)) * (c*x+d*y) = x
      calc
        _ = x * ((a*d-b*c) * (a*d-b*c)⁻¹) := by simp only [div_eq_mul_inv]; ring
        _ = x := by rw [mul_inv_cancel₀ hd, mul_one]
    · change (-c / (a*d-b*c)) * (a*x+b*y) + (a / (a*d-b*c)) * (c*x+d*y) = y
      calc
        _ = y * ((a*d-b*c) * (a*d-b*c)⁻¹) := by simp only [div_eq_mul_inv]; ring
        _ = y := by rw [mul_inv_cancel₀ hd, mul_one]
  have hLM : RightInverse M L := by
    rintro ⟨x, y⟩
    apply Prod.ext
    · change a * ((d / (a*d-b*c))*x+(-b / (a*d-b*c))*y) + b * ((-c / (a*d-b*c))*x+(a / (a*d-b*c))*y) = x
      calc
        _ = x * ((a*d-b*c) * (a*d-b*c)⁻¹) := by simp only [div_eq_mul_inv]; ring
        _ = x := by rw [mul_inv_cancel₀ hd, mul_one]
    · change c * ((d / (a*d-b*c))*x+(-b / (a*d-b*c))*y) + d * ((-c / (a*d-b*c))*x+(a / (a*d-b*c))*y) = y
      calc
        _ = y * ((a*d-b*c) * (a*d-b*c)⁻¹) := by simp only [div_eq_mul_inv]; ring
        _ = y := by rw [mul_inv_cancel₀ hd, mul_one]
  exact ⟨ContinuousLinearEquiv.equivOfInverse L M hML hLM, rfl⟩

theorem Family.e2_parameterColumn_contDiff {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (j : Fin (d+2)) :
    ContDiff ℝ ∞ (G.parameterColumn j) := by
  exact (ContinuousLinearMap.apply ℝ ℝ
    ((0, parameterFrame d (Pi.single j 1)) : ℝ × Parameters 2 d)).contDiff.comp
      (hG.fderiv_right (by simp))

def Family.e2SelectedPhaseGradient {d : ℕ} (G : Family 2 d) (σ : Fin 2 ↪ Fin (d+2))
    (z : Parameters 2 d × Plane) : Plane :=
  (z.2.2 * G.parameterColumn (σ 0) (z.2.1, z.1),
    z.2.2 * G.parameterColumn (σ 1) (z.2.1, z.1))

theorem Family.e2SelectedPhaseGradient_contDiff {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (σ : Fin 2 ↪ Fin (d+2)) : ContDiff ℝ ∞ (G.e2SelectedPhaseGradient σ) := by
  exact (contDiff_snd.snd.mul ((G.e2_parameterColumn_contDiff hG (σ 0)).comp
    (contDiff_snd.fst.prodMk contDiff_fst))).prodMk
    (contDiff_snd.snd.mul ((G.e2_parameterColumn_contDiff hG (σ 1)).comp
      (contDiff_snd.fst.prodMk contDiff_fst)))

theorem Family.e2_time_frequency_column_hasFDerivAt {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (j : Fin (d+2)) (q : Parameters 2 d) (x : Plane) :
    HasFDerivAt (fun w : Plane => w.2 * G.parameterColumn j (w.1, q))
      ((x.2 * timeDerivative (G.parameterColumn j) 1 (x.1, q)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        G.parameterColumn j (x.1, q) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  have hc : DifferentiableAt ℝ (G.parameterColumn j) (x.1, q) :=
    (G.e2_parameterColumn_contDiff hG j).contDiffAt.differentiableAt (by simp)
  have harg : HasFDerivAt (fun w : Plane => (w.1, q))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (0 : Plane →L[ℝ] Parameters 2 d)) x :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_const q x)
  have hh := hasFDerivAt_snd.mul (hc.hasFDerivAt.comp x harg)
  refine hh.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  change x.2 * (fderiv ℝ (G.parameterColumn j) (x.1, q) (v.1, 0)) +
        G.parameterColumn j (x.1, q) * v.2 =
      (x.2 * timeDerivative (G.parameterColumn j) 1 (x.1, q)) * v.1 +
        G.parameterColumn j (x.1, q) * v.2
  have hv : ((v.1, 0) : ℝ × Parameters 2 d) = v.1 • (1, 0) := by simp
  rw [hv, map_smul]
  change x.2 * (v.1 * fderiv ℝ (G.parameterColumn j) (x.1, q) (1, 0)) + _ =
    (x.2 * fderiv ℝ (G.parameterColumn j) (x.1, q) (1, 0)) * v.1 + _
  ring

theorem Family.e2SelectedPhaseGradient_hasFDerivAt {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (σ : Fin 2 ↪ Fin (d+2)) (q : Parameters 2 d) (x : Plane) :
    HasFDerivAt (fun w : Plane => G.e2SelectedPhaseGradient σ (q, w))
      (((x.2 * timeDerivative (G.parameterColumn (σ 0)) 1 (x.1, q)) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        G.parameterColumn (σ 0) (x.1, q) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      ((x.2 * timeDerivative (G.parameterColumn (σ 1)) 1 (x.1, q)) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        G.parameterColumn (σ 1) (x.1, q) • ContinuousLinearMap.snd ℝ ℝ ℝ)) x := by
  exact (G.e2_time_frequency_column_hasFDerivAt hG (σ 0) q x).prodMk
    (G.e2_time_frequency_column_hasFDerivAt hG (σ 1) q x)

theorem Family.e2SelectedPhaseGradient_fderiv_isInvertible {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (σ : Fin 2 ↪ Fin (d+2)) (q : Parameters 2 d) (x : Plane)
    (hη : x.2 ≠ 0)
    (hminor : G.cinematicInitialMinor (by omega : 2 ≤ d+2) σ (x.1, q) ≠ 0) :
    (fderiv ℝ (fun w : Plane => G.e2SelectedPhaseGradient σ (q, w)) x).IsInvertible := by
  rw [(G.e2SelectedPhaseGradient_hasFDerivAt hG σ q x).fderiv]
  apply e2_plane_two_by_two_isInvertible
  have hm : G.parameterColumn (σ 0) (x.1, q) *
          timeDerivative (G.parameterColumn (σ 1)) 1 (x.1, q) -
        G.parameterColumn (σ 1) (x.1, q) *
          timeDerivative (G.parameterColumn (σ 0)) 1 (x.1, q) ≠ 0 := by
    simpa [Family.cinematicInitialMinor, Matrix.det_fin_two, Family.cinematicMatrix,
      timeDerivative] using hminor
  have he : (x.2 * timeDerivative (G.parameterColumn (σ 0)) 1 (x.1, q)) *
        G.parameterColumn (σ 1) (x.1, q) -
      G.parameterColumn (σ 0) (x.1, q) *
        (x.2 * timeDerivative (G.parameterColumn (σ 1)) 1 (x.1, q)) =
      -x.2 * (G.parameterColumn (σ 0) (x.1, q) *
          timeDerivative (G.parameterColumn (σ 1)) 1 (x.1, q) -
        G.parameterColumn (σ 1) (x.1, q) *
          timeDerivative (G.parameterColumn (σ 0)) 1 (x.1, q)) := by ring
  rw [he]
  exact mul_ne_zero (neg_ne_zero.mpr hη) hm

theorem Family.exists_e2_cinematic_gradient_separation {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (q : Parameters 2 d) (x : Plane) (hη : x.2 ≠ 0)
    (hdet : G.cinematicDet (x.1, q) ≠ 0) :
    ∃ (σ : Fin 2 ↪ Fin (d+2)) (O : Set (Parameters 2 d × Plane)) (c : ℝ),
      IsOpen O ∧ (q, x) ∈ O ∧ 0 < c ∧
      ∀ (p : Parameters 2 d) (u v : Plane), (p, u) ∈ O → (p, v) ∈ O →
        c * ‖u-v‖ ≤ ‖G.e2SelectedPhaseGradient σ (p, u) -
          G.e2SelectedPhaseGradient σ (p, v)‖ := by
  obtain ⟨σ, hσ⟩ := G.exists_cinematicInitialMinor hdet 2 (by omega)
  obtain ⟨O, c, hO, hx, hc, hs⟩ := e2_exists_uniform_local_gradient_separation (x := (q, x))
    (G.e2SelectedPhaseGradient_contDiff hG σ)
    (G.e2SelectedPhaseGradient_fderiv_isInvertible hG σ q x hη hσ)
  exact ⟨σ, O, c, hO, hx, hc, hs⟩

theorem Family.e2SelectedTimeFrequencyPhase_fderiv_single {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (σ : Fin 2 ↪ Fin (d+2)) (v : Aux (d+2)) (q : Aux 2) (x : Plane) (j : Fin 2) :
    fderiv ℝ (fun u : Aux 2 => G.e2SelectedTimeFrequencyPhase σ v u x) q
        (Pi.single j 1) =
      x.2 * G.parameterColumn (σ j)
        (x.1, parameterFrame d (v + coordinateInsertion σ q)) := by
  have hγ : HasFDerivAt (fun z : ℝ × Parameters 2 d => G.γ z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Parameters 2 d => G.γ z.1 z.2)
        (x.1, parameterFrame d (v + coordinateInsertion σ q)))
      (x.1, parameterFrame d (v + coordinateInsertion σ q)) :=
    hG.differentiable (by simp) |>.differentiableAt.hasFDerivAt
  have harg : HasFDerivAt
      (fun u : Aux 2 => (x.1, parameterFrame d (v + coordinateInsertion σ u)))
      ((0 : Aux 2 →L[ℝ] ℝ).prod
        ((parameterFrame d).toContinuousLinearMap.comp (coordinateInsertion σ))) q := by
    exact (hasFDerivAt_const x.1 q).prodMk
      ((parameterFrame d).hasFDerivAt.comp q ((coordinateInsertion σ).hasFDerivAt.const_add v))
  have hh := (hγ.comp q harg).const_mul x.2
  change fderiv ℝ (fun u : Aux 2 =>
    x.2 * G.γ x.1 (parameterFrame d (v + coordinateInsertion σ u))) q _ = _
  have he := hh.fderiv
  dsimp only [Function.comp_def] at he
  rw [he]
  change x.2 * fderiv ℝ (fun z : ℝ × Parameters 2 d => G.γ z.1 z.2)
    (x.1, parameterFrame d (v + coordinateInsertion σ q))
    (0, parameterFrame d (coordinateInsertion σ (Pi.single j 1))) = _
  rw [coordinateInsertion_single]
  rfl

theorem Family.e2SelectedPhaseGradient_eq_selected_phase_gradient {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (σ : Fin 2 ↪ Fin (d+2)) (v : Aux (d+2)) (q : Aux 2) (x : Plane) :
    G.e2SelectedPhaseGradient σ
        (parameterFrame d (v + coordinateInsertion σ q), x) =
      (fderiv ℝ (fun u : Aux 2 => G.e2SelectedTimeFrequencyPhase σ v u x) q (Pi.single 0 1),
        fderiv ℝ (fun u : Aux 2 => G.e2SelectedTimeFrequencyPhase σ v u x) q (Pi.single 1 1)) := by
  exact Prod.ext (G.e2SelectedTimeFrequencyPhase_fderiv_single hG σ v q x 0).symm
    (G.e2SelectedTimeFrequencyPhase_fderiv_single hG σ v q x 1).symm

theorem Family.exists_e2_actual_phase_gradient_separation {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (q₀ : Parameters 2 d) (x : Plane) (hη : x.2 ≠ 0)
    (hdet : G.cinematicDet (x.1, q₀) ≠ 0) :
    ∃ (σ : Fin 2 ↪ Fin (d+2)) (O : Set (Parameters 2 d × Plane)) (c : ℝ),
      IsOpen O ∧ (q₀, x) ∈ O ∧ 0 < c ∧
      ∀ (v : Aux (d+2)) (q : Aux 2) (u w : Plane),
        (parameterFrame d (v + coordinateInsertion σ q), u) ∈ O →
        (parameterFrame d (v + coordinateInsertion σ q), w) ∈ O →
        c * ‖u-w‖ ≤ ‖
          (fderiv ℝ (fun z : Aux 2 => G.e2SelectedTimeFrequencyPhase σ v z u) q (Pi.single 0 1),
            fderiv ℝ (fun z : Aux 2 => G.e2SelectedTimeFrequencyPhase σ v z u) q (Pi.single 1 1)) -
          (fderiv ℝ (fun z : Aux 2 => G.e2SelectedTimeFrequencyPhase σ v z w) q (Pi.single 0 1),
            fderiv ℝ (fun z : Aux 2 => G.e2SelectedTimeFrequencyPhase σ v z w) q (Pi.single 1 1))‖ := by
  obtain ⟨σ, O, c, hO, hx, hc, hs⟩ := G.exists_e2_cinematic_gradient_separation hG q₀ x hη hdet
  refine ⟨σ, O, c, hO, hx, hc, ?_⟩
  intro v q u w hu hw
  rw [← G.e2SelectedPhaseGradient_eq_selected_phase_gradient hG σ v q u,
    ← G.e2SelectedPhaseGradient_eq_selected_phase_gradient hG σ v q w]
  exact hs _ u w hu hw

end PlanarNikodym
