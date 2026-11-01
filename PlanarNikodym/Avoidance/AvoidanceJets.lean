import PlanarNikodym.Projection.ProjectionModel
import PlanarNikodym.Rank.WronskianCriterion
import PlanarNikodym.Rank.FiniteEvaluation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Finite nondegeneracy certificates for the scalar model in §7.3.
The certificates below are derived from the actual parameter derivative.
They do not assume a separately supplied matrix of jets. -/

noncomputable section
open Set Filter Function MeasureTheory Metric
open scoped Topology Matrix
namespace PlanarNikodym.ProjectionModel

variable {d : ℕ} (D : ProjectionModel d)

/-- An ambient analytic extension of a coordinate parameter variation. -/
def variationColumn (j : Fin (d + 1)) (x : ℝ × Aux (d + 1)) : ℝ :=
  fderiv ℝ (fun y : ℝ × Aux (d + 1) => D.h y.1 y.2) x (0, Pi.single j 1)

theorem variationColumn_analyticAt {x : ℝ × Aux (d + 1)}
    (hx : x ∈ D.I.carrier ×ˢ ball D.base.2 D.radius) (j : Fin (d + 1)) :
    AnalyticAt ℝ (D.variationColumn j) x :=
  ((ContinuousLinearMap.apply ℝ ℝ
    ((0, Pi.single j 1) : ℝ × Aux (d + 1))).analyticAt _).comp (D.h_analytic x hx).fderiv

theorem variationColumn_eq (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius)
    (j : Fin (d + 1)) (t : D.I.carrier) :
    D.variationColumn j (t, w) =
      functionDerivative (fun s : D.I.carrier => D.h s) w (Pi.single j 1) t := by
  have he := fderiv_snd_slice (fun y : ℝ × Aux (d + 1) => D.h y.1 y.2)
    ((t : ℝ), w) (D.h_analytic (t, w) ⟨t.property, hw⟩).differentiableAt
  exact (congrArg (fun M : Aux (d + 1) →L[ℝ] ℝ => M (Pi.single j 1)) he).symm

theorem variationColumns_independent (w : Aux (d + 1))
    (hw : w ∈ ball D.base.2 D.radius) :
    LinearIndependent ℝ (fun j (t : D.I.carrier) => D.variationColumn j (t, w)) := by
  let L := functionDerivative (fun t : D.I.carrier => D.h t) w
  have hli := (Pi.basisFun ℝ (Fin (d + 1))).linearIndependent.map' L
    (LinearMap.ker_eq_bot.mpr (D.h_injective w hw))
  have he : (fun j (t : D.I.carrier) => D.variationColumn j (t, w)) =
      fun j => L (Pi.single j 1) := by
    ext j t
    exact D.variationColumn_eq w hw j t
  rw [he]
  simpa only [L, Function.comp_def, Pi.basisFun_apply] using hli

/-- The rank hypothesis has an explicit finite evaluation certificate. -/
theorem exists_variation_evaluation_det_ne_zero (w : Aux (d + 1))
    (hw : w ∈ ball D.base.2 D.radius) :
    ∃ t : Fin (d + 1) → D.I.carrier,
      Matrix.det (fun i j => D.variationColumn j (t i, w)) ≠ 0 :=
  exists_eval_det_ne_zero _ (D.variationColumns_independent w hw)

/-- The first `d + 1` time jets of the coordinate variations. -/
def variationJetMatrix (x : ℝ × Aux (d + 1)) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => timeDerivative (D.variationColumn j) i x

def variationJetDet (x : ℝ × Aux (d + 1)) : ℝ := (D.variationJetMatrix x).det

theorem variationJetDet_analytic :
    AnalyticOnNhd ℝ D.variationJetDet (D.I.carrier ×ˢ ball D.base.2 D.radius) := by
  intro x hx
  apply analyticAt_det
  intro i j
  exact timeDerivative_analyticAt (D.variationColumn_analyticAt hx j) i

theorem variationJetDet_eq_wronskian (w : Aux (d + 1))
    (hw : w ∈ ball D.base.2 D.radius) (t : ℝ) (ht : t ∈ D.I.carrier) :
    D.variationJetDet (t, w) =
      wronskian (fun j s => D.variationColumn j (s, w)) t := by
  unfold variationJetDet variationJetMatrix wronskian
  apply congrArg Matrix.det
  funext i j
  exact timeDerivative_eq_iteratedDeriv i (t, w)
    (D.variationColumn_analyticAt ⟨ht, hw⟩ j)

/-- Bôcher's theorem yields a nonzero finite jet determinant from the
injectivity of the genuine function-valued derivative. -/
theorem exists_variationJetDet_ne_zero (w : Aux (d + 1))
    (hw : w ∈ ball D.base.2 D.radius) :
    ∃ t ∈ D.I.carrier, D.variationJetDet (t, w) ≠ 0 := by
  have ha : ∀ j, AnalyticOnNhd ℝ (fun t => D.variationColumn j (t, w)) D.I.carrier := by
    intro j t ht
    exact (D.variationColumn_analyticAt ⟨ht, hw⟩ j).comp
      (f := fun t : ℝ => (t, w)) (analyticAt_id.prod analyticAt_const)
  obtain ⟨t, ht, hn⟩ := bocher_input (d + 1) D.I _ ha
    (D.variationColumns_independent w hw)
  exact ⟨t, ht, by rwa [D.variationJetDet_eq_wronskian w hw t ht]⟩

theorem exists_interior_variationJetDet_ne_zero (w : Aux (d + 1))
    (hw : w ∈ ball D.base.2 D.radius) :
    ∃ t ∈ Ioo D.I.left D.I.right, D.variationJetDet (t, w) ≠ 0 := by
  apply exists_interior_ne_zero D.I (fun t => D.variationJetDet (t, w))
  · intro t ht
    exact ((D.variationJetDet_analytic (t, w) ⟨ht, hw⟩).comp
      (f := fun t : ℝ => (t, w)) (analyticAt_id.prod analyticAt_const)).continuousAt
  · exact D.exists_variationJetDet_ne_zero w hw

/-- Each parameter has only finitely many degenerate times, including at
the endpoints of the closed time interval. -/
theorem variationJetDet_zeros_finite (w : Aux (d + 1))
    (hw : w ∈ ball D.base.2 D.radius) :
    {t | t ∈ D.I.carrier ∧ D.variationJetDet (t, w) = 0}.Finite := by
  apply analytic_zeros_finite_interval D.I
  · intro t ht
    exact (D.variationJetDet_analytic (t, w) ⟨ht, hw⟩).comp
      (f := fun t : ℝ => (t, w)) (analyticAt_id.prod analyticAt_const)
  · exact D.exists_variationJetDet_ne_zero w hw

theorem variationJetDet_ne_zero_ae (w : Aux (d + 1))
    (hw : w ∈ ball D.base.2 D.radius) :
    ∀ᵐ t ∂volume.restrict D.I.carrier, D.variationJetDet (t, w) ≠ 0 := by
  rw [ae_restrict_iff' (show MeasurableSet D.I.carrier from measurableSet_Icc)]
  have hz := (D.variationJetDet_zeros_finite w hw).countable.measure_zero volume
  apply ae_iff.mpr
  simpa only [Classical.not_imp, not_not] using hz

/-- At a nondegenerate time, the finite jet matrix detects every parameter
direction: vanishing of all its rows forces that direction to be zero. -/
theorem variationJetMatrix_detects_direction (x : ℝ × Aux (d + 1))
    (hx : D.variationJetDet x ≠ 0) (v : Aux (d + 1))
    (hv : ∀ i, ∑ j, timeDerivative (D.variationColumn j) i x * v j = 0) : v = 0 := by
  have hi : Injective (D.variationJetMatrix x).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx))
  apply hi
  ext i
  simpa only [variationJetMatrix, Matrix.mulVec, dotProduct, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero] using hv i

/-- Joint degeneracy, restricted to the domain on which the scalar model
is analytic. -/
def variationJetDegenerateSet : Set (ℝ × Aux (d + 1)) :=
  {x | x ∈ D.I.carrier ×ˢ ball D.base.2 D.radius ∧ D.variationJetDet x = 0}

theorem measurableSet_variationJetDegenerateSet :
    MeasurableSet D.variationJetDegenerateSet := by
  classical
  let S := D.I.carrier ×ˢ ball D.base.2 D.radius
  have hS : MeasurableSet S := measurableSet_Icc.prod isOpen_ball.measurableSet
  have hm : Measurable (S.piecewise D.variationJetDet (fun _ => (0 : ℝ))) :=
    D.variationJetDet_analytic.continuousOn.measurable_piecewise
      (g := fun _ => (0 : ℝ)) continuousOn_const hS
  have he : D.variationJetDegenerateSet = S ∩
      {x | S.piecewise D.variationJetDet (fun _ => (0 : ℝ)) x = 0} := by
    ext x
    change (x ∈ S ∧ D.variationJetDet x = 0) ↔
      x ∈ S ∧ S.piecewise D.variationJetDet (fun _ => (0 : ℝ)) x = 0
    by_cases hx : x ∈ S <;> simp [hx]
  rw [he]
  exact hS.inter (measurableSet_eq_fun hm measurable_const)

/-- Fubini applied to the finite exceptional sets: joint jet degeneracy
has zero product measure. -/
theorem variationJetDegenerateSet_null :
    (volume.prod volume) D.variationJetDegenerateSet = 0 := by
  rw [Measure.prod_apply_symm D.measurableSet_variationJetDegenerateSet]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro w
  change volume ((fun t : ℝ => (t, w)) ⁻¹' D.variationJetDegenerateSet) = 0
  by_cases hw : w ∈ ball D.base.2 D.radius
  · have he : (fun t : ℝ => (t, w)) ⁻¹' D.variationJetDegenerateSet =
        {t | t ∈ D.I.carrier ∧ D.variationJetDet (t, w) = 0} := by
      ext t
      simp only [variationJetDegenerateSet, mem_preimage, mem_setOf_eq, mem_prod,
        hw, and_true]
    rw [he]
    exact (D.variationJetDet_zeros_finite w hw).countable.measure_zero volume
  · have he : (fun t : ℝ => (t, w)) ⁻¹' D.variationJetDegenerateSet = ∅ := by
      ext t
      simp only [variationJetDegenerateSet, mem_preimage, mem_setOf_eq, mem_prod,
        hw, and_false, false_and, mem_empty_iff_false]
    rw [he, measure_empty]

/-- The time-first Fubini conclusion needed to choose a common time for
almost all parameters. -/
theorem variationJetDet_ne_zero_ae_parameters_ae_time :
    ∀ᵐ t ∂volume.restrict D.I.carrier,
      ∀ᵐ w ∂volume.restrict (ball D.base.2 D.radius), D.variationJetDet (t, w) ≠ 0 := by
  rw [ae_restrict_iff' (show MeasurableSet D.I.carrier from measurableSet_Icc)]
  have hf := Measure.measure_ae_null_of_prod_null D.variationJetDegenerateSet_null
  filter_upwards [hf] with t ht hI
  rw [ae_restrict_iff' isOpen_ball.measurableSet]
  apply ae_iff.mpr
  have he : {w | ¬(w ∈ ball D.base.2 D.radius → D.variationJetDet (t, w) ≠ 0)} =
      Prod.mk t ⁻¹' D.variationJetDegenerateSet := by
    ext w
    simp [variationJetDegenerateSet, hI]
  rwa [he]

theorem analytic_directional_derivatives_commute {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {x : E} (hf : AnalyticAt ℝ f x) (u v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y u) x v =
      fderiv ℝ (fun y => fderiv ℝ f y v) x u := by
  rw [fderiv_clm_apply hf.fderiv.differentiableAt (differentiableAt_const u),
    fderiv_clm_apply hf.fderiv.differentiableAt (differentiableAt_const v)]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using hf.contDiffAt.isSymmSndFDerivAt_of_omega v u

/-- Time differentiation commutes with any fixed ambient parameter
variation. This identifies the finite matrix with an actual jet derivative. -/
theorem timeDerivative_fderiv_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ × E → ℝ} {x : ℝ × E} (hf : AnalyticAt ℝ f x)
    (k : ℕ) (v : ℝ × E) :
    timeDerivative (fun y => fderiv ℝ f y v) k x =
      fderiv ℝ (timeDerivative f k) x v := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have he : timeDerivative (fun y => fderiv ℝ f y v) k =ᶠ[𝓝 x]
        fun y => fderiv ℝ (timeDerivative f k) y v := by
      filter_upwards [hf.eventually_analyticAt] with y hy
      exact ih hy
    change fderiv ℝ (timeDerivative (fun y => fderiv ℝ f y v) k) x (1, 0) = _
    rw [he.fderiv_eq]
    exact analytic_directional_derivatives_commute (timeDerivative_analyticAt hf k) v (1, 0)

/-- The genuine finite jet map of the scalar family. -/
def timeJet (t : ℝ) (w : Aux (d + 1)) : Fin (d + 1) → ℝ :=
  fun i => timeDerivative (fun y : ℝ × Aux (d + 1) => D.h y.1 y.2) i (t, w)

theorem timeJet_analyticAt (t : ℝ) (ht : t ∈ D.I.carrier)
    (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius) :
    AnalyticAt ℝ (D.timeJet t) w := by
  apply AnalyticAt.pi
  intro i
  exact (timeDerivative_analyticAt (D.h_analytic (t, w) ⟨ht, hw⟩) i).comp
    (f := fun w : Aux (d + 1) => (t, w)) (analyticAt_const.prod analyticAt_id)

/-- Entries of the variation matrix are the actual coordinate derivatives
of the finite time jet. -/
theorem variationJetMatrix_eq_timeJet_derivative (t : ℝ) (ht : t ∈ D.I.carrier)
    (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius)
    (i j : Fin (d + 1)) :
    D.variationJetMatrix (t, w) i j =
      fderiv ℝ (fun w => D.timeJet t w i) w (Pi.single j 1) := by
  change timeDerivative (fun y => fderiv ℝ (fun z : ℝ × Aux (d + 1) =>
    D.h z.1 z.2) y (0, Pi.single j 1)) i (t, w) = _
  rw [timeDerivative_fderiv_apply (D.h_analytic (t, w) ⟨ht, hw⟩)]
  have he := fderiv_snd_slice
    (timeDerivative (fun z : ℝ × Aux (d + 1) => D.h z.1 z.2) i)
      (t, w) (timeDerivative_analyticAt (D.h_analytic (t, w) ⟨ht, hw⟩) i).differentiableAt
  exact (congrArg (fun L : Aux (d + 1) →L[ℝ] ℝ => L (Pi.single j 1)) he).symm

theorem timeJet_fderiv_matrix (t : ℝ) (ht : t ∈ D.I.carrier)
    (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius) :
    LinearMap.toMatrix' (fderiv ℝ (D.timeJet t) w).toLinearMap =
      D.variationJetMatrix (t, w) := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  have he := fderiv_apply (D.timeJet_analyticAt t ht w hw).differentiableAt i
  calc
    (fderiv ℝ (D.timeJet t) w) (Pi.single j 1) i =
        fderiv ℝ (fun w => D.timeJet t w i) w (Pi.single j 1) :=
      (congrArg (fun L : Aux (d + 1) →L[ℝ] ℝ => L (Pi.single j 1)) he).symm
    _ = D.variationJetMatrix (t, w) i j :=
      (D.variationJetMatrix_eq_timeJet_derivative t ht w hw i j).symm

/-- The scalar model has an injective genuine finite-jet derivative at
every nondegenerate time. -/
theorem timeJet_fderiv_injective (t : ℝ) (ht : t ∈ D.I.carrier)
    (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius)
    (hdet : D.variationJetDet (t, w) ≠ 0) :
    Injective (fderiv ℝ (D.timeJet t) w) := by
  have hi : Injective (D.variationJetMatrix (t, w)).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  have he (v : Aux (d + 1)) :
      (D.variationJetMatrix (t, w)).mulVec v = fderiv ℝ (D.timeJet t) w v := by
    rw [← D.timeJet_fderiv_matrix t ht w hw, LinearMap.toMatrix'_mulVec]
    rfl
  intro v u hvu
  apply hi
  rw [he, he]
  exact hvu

theorem timeJet_fderiv_injective_ae (w : Aux (d + 1))
    (hw : w ∈ ball D.base.2 D.radius) :
    ∀ᵐ t ∂volume.restrict D.I.carrier, Injective (fderiv ℝ (D.timeJet t) w) := by
  filter_upwards [D.variationJetDet_ne_zero_ae w hw,
    ae_restrict_mem (show MeasurableSet D.I.carrier from measurableSet_Icc)] with t hdet ht
  exact D.timeJet_fderiv_injective t ht w hw hdet

end PlanarNikodym.ProjectionModel
