import PlanarNikodym.Geometry.ParametricAnalyticCoordinates
import PlanarNikodym.Analysis.Fourier.TimeTaylorApproximation
import PlanarNikodym.Geometry.MovingCinematicCoordinates
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Banach

/-! Smooth inverse charts and genuine smooth time-jet coordinates.
No analyticity assumption enters these constructions. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace PlanarNikodym

/-- A C∞ map with an invertible derivative has a C∞ local inverse,
with the source inside any prescribed neighborhood. -/
theorem exists_glyz_smooth_chart {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → E) (hf : ContDiff ℝ ∞ f) (x : E)
    (hi : (fderiv ℝ f x).IsInvertible) (U : Set E) (hU : U ∈ 𝓝 x) :
    ∃ e : OpenPartialHomeomorph E E, x ∈ e.source ∧ e.source ⊆ U ∧
      (∀ y, e y = f y) ∧ (∀ y ∈ e.source, ContDiffAt ℝ ∞ e y) ∧
        ∀ y ∈ e.target, ContDiffAt ℝ ∞ e.symm y := by
  obtain ⟨L, hL⟩ := hi
  have hd : HasFDerivAt f (L : E →L[ℝ] E) x := hL ▸ (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
  let e₀ := hf.contDiffAt.toOpenPartialHomeomorph f hd (by simp)
  have hx : x ∈ e₀.source := hf.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  let V : Set E := {y | IsUnit (fderiv ℝ f y)}
  have hV : IsOpen V := Units.isOpen.preimage (hf.continuous_fderiv (by simp))
  have hxV : x ∈ V := by
    apply ContinuousLinearMap.isUnit_iff_bijective.mpr
    rw [← hL]
    exact L.bijective
  obtain ⟨S, hSU, hS, hxS⟩ := mem_nhds_iff.mp (inter_mem hU (hV.mem_nhds hxV))
  refine ⟨e₀.restr S, ?_, ?_, fun _ => rfl, fun _ _ => hf.contDiffAt, ?_⟩
  · rw [e₀.restr_source' S hS]
    exact ⟨hx, hxS⟩
  · intro y hy
    exact (hSU ((e₀.restr_source' S hS) ▸ hy).2).1
  · intro y hy
    have hz := (e₀.restr S).map_target hy
    have hunit := (hSU ((e₀.restr_source' S hS) ▸ hz).2).2
    obtain ⟨u, hu⟩ := hunit
    let T : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit u
    have hT : (T : E →L[ℝ] E) = fderiv ℝ f ((e₀.restr S).symm y) := hu
    apply (e₀.restr S).contDiffAt_symm hy
    · change HasFDerivAt f (T : E →L[ℝ] E) _
      rw [hT]
      exact (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
    · exact hf.contDiffAt

theorem exists_glyz_retained_smooth_chart
    {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace P] [CompleteSpace E]
    {F : P × E → E} (hF : ContDiff ℝ ∞ F) {x : P × E}
    (hi : (fderiv ℝ (fun z => F (x.1, z)) x.2).IsInvertible)
    (U : Set (P × E)) (hU : U ∈ 𝓝 x) :
    ∃ e : OpenPartialHomeomorph (P × E) (P × E),
      x ∈ e.source ∧ e.source ⊆ U ∧ (∀ z, e z = (z.1, F z)) ∧
      (∀ y ∈ e.source, ContDiffAt ℝ ∞ e y) ∧
      (∀ y ∈ e.target, ContDiffAt ℝ ∞ e.symm y) ∧
      ∀ y ∈ e.target, (e.symm y).1 = y.1 ∧ F (e.symm y) = y.2 := by
  obtain ⟨e, hx, hsub, he, ha, hb⟩ := exists_glyz_smooth_chart (retainedParameterMap F)
    (contDiff_fst.prodMk hF) x
    (retainedParameterMap_fderiv_isInvertible (hF.differentiable (by simp)).differentiableAt hi) U hU
  refine ⟨e, hx, hsub, he, ha, hb, fun y hy => ?_⟩
  have hr := e.right_inv hy
  rw [he] at hr
  change ((e.symm y).1, F (e.symm y)) = y at hr
  have hp := congrArg (fun z : P × E => z.1) hr
  have hz := congrArg (fun z : P × E => z.2) hr
  exact ⟨hp, hz⟩

theorem contDiff_timeDerivative {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (timeDerivative f k) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    exact (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × E)).contDiff.comp
      (ih.fderiv_right (by simp))

theorem timeDerivative_eq_iteratedDeriv_of_contDiff
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : ℝ × E) :
    timeDerivative f k x = iteratedDeriv k (fun t => f (t, x.2)) x.1 := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have hd := ((contDiff_timeDerivative hf k).differentiable (by simp)).differentiableAt (x := x)
    have hs := fderiv_fst_slice (timeDerivative f k) x hd
    change ((fderiv ℝ (timeDerivative f k) x).comp (ContinuousLinearMap.inl ℝ ℝ E)) 1 = _
    rw [← hs]
    change deriv (fun t => timeDerivative f k (t, x.2)) x.1 = _
    rw [iteratedDeriv_succ]
    congr 1
    funext t
    exact ih (t, x.2)

theorem glyz_smooth_directional_derivatives_commute {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (x u v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y u) x v =
      fderiv ℝ (fun y => fderiv ℝ f y v) x u := by
  have hD := ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt (x := x)
  rw [fderiv_clm_apply hD (differentiableAt_const u),
    fderiv_clm_apply hD (differentiableAt_const v)]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using hf.contDiffAt.isSymmSndFDerivAt (by
      norm_num [minSmoothness]
      exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)) v u

theorem glyz_smooth_timeDerivative_fderiv_apply {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ × E → ℝ}
    (hf : ContDiff ℝ ∞ f) (k : ℕ) (x v : ℝ × E) :
    timeDerivative (fun y => fderiv ℝ f y v) k x = fderiv ℝ (timeDerivative f k) x v := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have he : timeDerivative (fun y => fderiv ℝ f y v) k =
        fun y => fderiv ℝ (timeDerivative f k) y v := funext ih
    change fderiv ℝ (timeDerivative (fun y => fderiv ℝ f y v) k) x (1, 0) = _
    rw [he]
    exact glyz_smooth_directional_derivatives_commute (contDiff_timeDerivative hf k) x v (1, 0)

theorem Family.cinematicJetMap_contDiff {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (t : ℝ) :
    ContDiff ℝ ∞ (G.cinematicJetMap t) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_timeDerivative hG i).comp (contDiff_const.prodMk (parameterFrame d).contDiff)

theorem Family.cinematicMatrix_eq_jet_fderiv_smooth {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (t : ℝ) (v : Aux (d + 2)) (i j : Fin (d + 2)) :
    G.cinematicMatrix (t, parameterFrame d v) i j =
      fderiv ℝ (fun w => G.cinematicJetMap t w i) v (Pi.single j 1) := by
  let F : ℝ × Parameters 2 d → ℝ := fun x => G.γ x.1 x.2
  change timeDerivative (fun x => fderiv ℝ F x
    (0, parameterFrame d (Pi.single j 1))) i (t, parameterFrame d v) = _
  rw [glyz_smooth_timeDerivative_fderiv_apply hG]
  have hT := contDiff_timeDerivative hG i
  have hslice : ContDiff ℝ ∞ (fun p : Parameters 2 d => timeDerivative F i (t, p)) :=
    hT.comp (contDiff_const.prodMk contDiff_id)
  have hchain : fderiv ℝ (fun w : Aux (d + 2) =>
      timeDerivative F i (t, parameterFrame d w)) v =
      (fderiv ℝ (fun p : Parameters 2 d => timeDerivative F i (t, p))
        (parameterFrame d v)).comp (parameterFrame d).toContinuousLinearMap :=
    ((hslice.differentiable (by simp)).differentiableAt.hasFDerivAt.comp v
      (parameterFrame d).toContinuousLinearMap.hasFDerivAt).fderiv
  change fderiv ℝ (timeDerivative F i) (t, parameterFrame d v)
    (0, parameterFrame d (Pi.single j 1)) =
      fderiv ℝ (fun w => timeDerivative F i (t, parameterFrame d w)) v (Pi.single j 1)
  rw [hchain, fderiv_snd_slice (timeDerivative F i) (t, parameterFrame d v)
    ((hT.differentiable (by simp)).differentiableAt)]
  rfl

theorem Family.movingLowerJetMap_contDiff {d m : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (hm : m ≤ d + 2) (σ : Fin m ↪ Fin (d + 2)) :
    ContDiff ℝ ∞ (G.movingLowerJetMap hm σ) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_timeDerivative hG (Fin.castLE hm i)).comp
    (contDiff_fst.fst.prodMk ((parameterFrame d).contDiff.comp
      (contDiff_fst.snd.add ((coordinateInsertion σ).contDiff.comp contDiff_snd))))

theorem Family.lowerCinematicJetMap_fderiv_matrix_smooth {d m : ℕ} (G : Family 2 d)
    (hm : m ≤ d + 2) (σ : Fin m ↪ Fin (d + 2))
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (t : ℝ) (v : Aux (d + 2)) :
    LinearMap.toMatrix' (fderiv ℝ (G.lowerCinematicJetMap hm σ t v) 0).toLinearMap =
      fun i j => G.cinematicMatrix (t, parameterFrame d v) (Fin.castLE hm i) (σ j) := by
  have hlc : ContDiff ℝ ∞ (G.lowerCinematicJetMap hm σ t v) := by
    change ContDiff ℝ ∞ (G.movingLowerJetMap hm σ ∘ fun z => ((t, v), z))
    exact (G.movingLowerJetMap_contDiff hG hm σ).comp (contDiff_const.prodMk contDiff_id)
  have hl : DifferentiableAt ℝ (G.lowerCinematicJetMap hm σ t v) 0 :=
    (hlc.differentiable (by simp)).differentiableAt
  ext i j
  rw [LinearMap.toMatrix'_apply]
  have hfull : ContDiff ℝ ∞ (fun w => G.cinematicJetMap t w (Fin.castLE hm i)) :=
    (contDiff_pi.mp (G.cinematicJetMap_contDiff hG t)) (Fin.castLE hm i)
  have hd : HasFDerivAt (fun w => G.cinematicJetMap t w (Fin.castLE hm i))
      (fderiv ℝ (fun w => G.cinematicJetMap t w (Fin.castLE hm i)) v)
      (v + coordinateInsertion σ 0) := by
    simpa only [map_zero, add_zero] using (hfull.differentiable (by simp)).differentiableAt.hasFDerivAt (x := v)
  have hchain := (hd.comp 0 ((coordinateInsertion σ).hasFDerivAt.const_add v)).fderiv
  dsimp only [Function.comp_def] at hchain
  have he := fderiv_apply hl i
  calc
    (fderiv ℝ (G.lowerCinematicJetMap hm σ t v) 0) (Pi.single j 1) i =
        fderiv ℝ (fun z => G.lowerCinematicJetMap hm σ t v z i) 0 (Pi.single j 1) :=
      (congrArg (fun L : Aux m →L[ℝ] ℝ => L (Pi.single j 1)) he).symm
    _ = fderiv ℝ (fun w => G.cinematicJetMap t w (Fin.castLE hm i)) v
        (Pi.single (σ j) 1) := by
      change fderiv ℝ (fun z => G.cinematicJetMap t (v + coordinateInsertion σ z)
        (Fin.castLE hm i)) 0 (Pi.single j 1) = _
      rw [hchain]
      change (fderiv ℝ (fun w => G.cinematicJetMap t w (Fin.castLE hm i)) v)
        (coordinateInsertion σ (Pi.single j 1)) = _
      rw [coordinateInsertion_single]
    _ = G.cinematicMatrix (t, parameterFrame d v) (Fin.castLE hm i) (σ j) :=
      (G.cinematicMatrix_eq_jet_fderiv_smooth hG t v (Fin.castLE hm i) (σ j)).symm

/-- The actual cinematic determinant supplies the lower time-jet
chart under C∞ regularity alone. -/
theorem Family.exists_movingLowerJet_smooth_chart {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {t : ℝ} {v : Aux (d + 2)} (hdet : G.cinematicDet (t, parameterFrame d v) ≠ 0)
    (m : ℕ) (hm : m ≤ d + 2) (U : Set ((ℝ × Aux (d + 2)) × Aux m))
    (hU : U ∈ 𝓝 ((t, v), (0 : Aux m))) :
    ∃ (σ : Fin m ↪ Fin (d + 2))
      (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux m)
        ((ℝ × Aux (d + 2)) × Aux m)),
      ((t, v), (0 : Aux m)) ∈ e.source ∧ e.source ⊆ U ∧
      (∀ x, e x = (x.1, G.movingLowerJetMap hm σ x)) ∧
      (∀ x ∈ e.source, ContDiffAt ℝ ∞ e x) ∧
      (∀ x ∈ e.target, ContDiffAt ℝ ∞ e.symm x) ∧
      ∀ y ∈ e.target, (e.symm y).1 = y.1 ∧ G.movingLowerJetMap hm σ (e.symm y) = y.2 := by
  obtain ⟨σ, hσ⟩ := G.exists_cinematicInitialMinor hdet m hm
  have hi : (fderiv ℝ (G.lowerCinematicJetMap hm σ t v) 0).IsInvertible := by
    apply isInvertible_of_det_coordinates
    change (LinearMap.toMatrix' (fderiv ℝ (G.lowerCinematicJetMap hm σ t v) 0).toLinearMap).det ≠ 0
    rw [G.lowerCinematicJetMap_fderiv_matrix_smooth hm σ hG]
    exact hσ
  obtain ⟨e, he⟩ := exists_glyz_retained_smooth_chart (G.movingLowerJetMap_contDiff hG hm σ)
    (x := ((t, v), (0 : Aux m))) hi U hU
  exact ⟨σ, e, he⟩

end PlanarNikodym
