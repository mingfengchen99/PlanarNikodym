import PlanarNikodym.Geometry.CenterCoordinates
import PlanarNikodym.Geometry.NullGeometry

noncomputable section
open Set Filter Module Function MeasureTheory
open scoped Topology
namespace PlanarNikodym

/-- An injective derivative into a space of functions is detected by finitely
many evaluations. The resulting finite evaluation map is locally injective. -/
theorem exists_injective_evaluations_near {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : X → E → ℝ) (q : E) (ha : ∀ t, AnalyticAt ℝ (f t) q)
    (hi : Injective (functionDerivative f q)) :
    ∃ U : Set E, IsOpen U ∧ q ∈ U ∧
      ∀ p ∈ U, ∀ r ∈ U, (∀ t, f t p = f t r) → p = r := by
  classical
  let n := finrank ℝ E
  let e : (Fin n → ℝ) ≃L[ℝ] E := (Module.finBasis ℝ E).equivFunL.symm
  let g : X → (Fin n → ℝ) → ℝ := fun t p => f t (e p)
  let q' := e.symm q
  have hq : e q' = q := e.apply_symm_apply q
  have hg : ∀ t, AnalyticAt ℝ (g t) q' := by
    intro t
    exact (hq ▸ ha t).comp (e.analyticAt q')
  have hD : Injective (functionDerivative g q') := by
    rw [functionDerivative_comp f e q' (by simpa only [hq] using fun t => (ha t).differentiableAt)
      e.differentiableAt, e.fderiv]
    rw [hq]
    exact hi.comp e.injective
  have hli := (Pi.basisFun ℝ (Fin n)).linearIndependent.map'
    (functionDerivative g q') (LinearMap.ker_eq_bot.mpr hD)
  obtain ⟨x, hx⟩ := exists_eval_det_ne_zero
    (fun j => functionDerivative g q' (Pi.single j 1))
    (by simpa only [Function.comp_def, Pi.basisFun_apply] using hli)
  let F : (Fin n → ℝ) → (Fin n → ℝ) := fun p i => g (x i) p
  have hF : AnalyticAt ℝ F q' := AnalyticAt.pi (fun i => hg (x i))
  have hFi : (fderiv ℝ F q').IsInvertible := by
    apply isInvertible_of_det_coordinates
    rw [fderiv_pi (fun i => (hg (x i)).differentiableAt)]
    exact hx
  obtain ⟨C, hqC, _, he, _, _⟩ := exists_analytic_chart F q' hF hFi univ (by simp)
  refine ⟨e '' C.source, e.toHomeomorph.isOpenMap _ C.open_source,
    ⟨q', hqC, hq⟩, ?_⟩
  rintro p ⟨p', hp, rfl⟩ r ⟨r', hr, rfl⟩ h
  apply congrArg e
  apply C.injOn hp hr
  rw [he, he]
  exact funext (fun i => h (x i))

/-- Full function rank forces every curve fibre in parameter space to be
discrete and hence countable. This avoids any Wronskian assumption. -/
theorem full_curve_rank_parameters_countable {d : ℕ} (G : Family 2 d)
    (ha : G.IsAnalytic) (hc : ∀ p ∈ G.W, G.curveRank p = d + 2)
    (β : Set Plane) : (G.parametersOf β).Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  apply isDiscrete_iff_forall_exists_isOpen.mpr
  intro q hq
  have hf := fun t : G.I.carrier => (G.parameter_analytic ha q hq.1 t).differentiableAt
  let L := functionDerivative (fun (t : G.I.carrier) => G.γ t) q
  have hr : finrank ℝ L.range = finrank ℝ (Parameters 2 d) := by
    rw [← G.curveSpace_eq_range q hf]
    simpa only [Module.finrank_prod, Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      mul_one, Nat.add_comm] using (show finrank ℝ (G.curveSpace q) = d + 2 from hc q hq.1)
  have hk := L.finrank_range_add_finrank_ker
  have hker : L.ker = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  obtain ⟨U, hUo, hqU, hU⟩ := exists_injective_evaluations_near
    (fun (t : G.I.carrier) => G.γ t) q (G.parameter_analytic ha q hq.1)
    (LinearMap.ker_eq_bot.mp hker)
  refine ⟨U, hUo, ?_⟩
  ext p
  constructor
  · rintro ⟨hpU, hp⟩
    apply mem_singleton_iff.mpr
    apply hU p hpU q hqU
    intro t
    exact (G.sameCurve_iff_curve_eq p q).mpr (hp.2.trans hq.2.symm) t t.property
  · rintro rfl
    exact ⟨hqU, hq⟩

theorem full_curve_rank_centers_countable {d : ℕ} (G : Family 2 d)
    (ha : G.IsAnalytic) (hc : ∀ p ∈ G.W, G.curveRank p = d + 2)
    (β : Set Plane) : (G.centersOf β).Countable :=
  (full_curve_rank_parameters_countable G ha hc β).image Prod.fst

theorem full_curve_rank_not_reused {d : ℕ} (G : Family 2 d)
    (ha : G.IsAnalytic) (hc : ∀ p ∈ G.W, G.curveRank p = d + 2)
    (β : Set Plane) : ¬ G.Reused β := by
  haveI := Measure.noAtoms_hausdorff (Base 2) (by norm_num : (0 : ℝ) < 1)
  rintro ⟨A, hA, _, hp⟩
  exact hp.ne' (measure_mono_null hA
    ((full_curve_rank_centers_countable G ha hc β).measure_zero
      (Measure.hausdorffMeasure 1)))

end PlanarNikodym
