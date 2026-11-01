import PlanarNikodym.Core.Definitions
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.DiscreteSubset

/-! Nullity of regular scalar level sets, using only one-dimensional
isolated zeros and coordinate Fubini. No implicit-function theorem or
regularity beyond actual differentiability at the relevant points is used. -/

noncomputable section
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
namespace PlanarNikodym

theorem regular_real_zeros_countable (f : ℝ → ℝ) :
    {x | f x = 0 ∧ deriv f x ≠ 0}.Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  apply isDiscrete_iff_nhdsNE.mpr
  intro x hx
  rw [Filter.inf_principal_eq_bot]
  have he : ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 :=
    (differentiableAt_of_deriv_ne_zero hx.2).hasDerivAt.eventually_ne hx.2
  exact he.mono (fun y hy => fun hmem => hy hmem.1)

theorem hasDerivAt_insertNth {n : ℕ} (j : Fin (n + 1)) (w : Aux n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => j.insertNth (α := fun _ => ℝ) s w) (Pi.single j 1) t := by
  have h := ((hasDerivAt_id t).smul_const (Pi.single j (1 : ℝ) : Aux (n + 1))).add_const
    (j.insertNth (α := fun _ => ℝ) 0 w)
  convert h using 1 <;> try rfl
  all_goals try simp only [one_smul]
  funext s k
  by_cases hk : k = j
  · subst k
    simp
  · simp [Fin.insertNth, Fin.succAboveCases, hk]

/-- The part of a scalar zero set on which one coordinate derivative is
nonzero has zero Lebesgue measure. The ambient function need only be Borel. -/
theorem regular_coordinate_zero_set_null {n : ℕ} (f : Aux (n + 1) → ℝ)
    (hf : Measurable f) (j : Fin (n + 1)) :
    volume {x | f x = 0 ∧ fderiv ℝ f x (Pi.single j 1) ≠ 0} = 0 := by
  let S := {x | f x = 0 ∧ fderiv ℝ f x (Pi.single j 1) ≠ 0}
  have hS : MeasurableSet S := (measurableSet_eq_fun hf measurable_const).inter
    (measurableSet_eq_fun (measurable_fderiv_apply_const ℝ f (Pi.single j 1))
      measurable_const).compl
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).symm
  rw [← hmp.measure_preimage hS.nullMeasurableSet]
  change (volume.prod volume) (e.symm ⁻¹' S) = 0
  rw [Measure.prod_apply_symm (hS.preimage e.symm.measurable)]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro w
  change volume ((fun t : ℝ => (t, w)) ⁻¹' (e.symm ⁻¹' S)) = 0
  apply measure_mono_null (t := {t | f (j.insertNth t w) = 0 ∧
    deriv (fun s => f (j.insertNth s w)) t ≠ 0})
  · intro t ht
    change f (j.insertNth t w) = 0 ∧
      fderiv ℝ f (j.insertNth t w) (Pi.single j 1) ≠ 0 at ht
    refine ⟨ht.1, ?_⟩
    have hd : DifferentiableAt ℝ f (j.insertNth t w) := by
      by_contra hn
      exact ht.2 (by rw [fderiv_zero_of_not_differentiableAt hn]; rfl)
    change deriv (f ∘ fun s => j.insertNth s w) t ≠ 0
    rw [(hd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_insertNth j w t)).deriv]
    exact ht.2
  · exact (regular_real_zeros_countable _).measure_zero volume

/-- Every regular scalar zero set of a Borel function on finite-dimensional
coordinate space is null. This also handles functions with irregular
ambient extensions outside their intended domain. -/
theorem regular_zero_set_null {n : ℕ} (f : Aux (n + 1) → ℝ)
    (hf : Measurable f) : volume {x | f x = 0 ∧ fderiv ℝ f x ≠ 0} = 0 := by
  apply measure_mono_null (t := ⋃ j : Fin (n + 1),
    {x | f x = 0 ∧ fderiv ℝ f x (Pi.single j 1) ≠ 0})
  · intro x hx
    apply mem_iUnion.mpr
    by_contra! hn
    have hzero : (fderiv ℝ f x).toLinearMap = 0 := by
      apply (Pi.basisFun ℝ (Fin (n + 1))).ext
      intro j
      simp only [Pi.basisFun_apply, LinearMap.zero_apply]
      by_contra hh
      exact hn j ⟨hx.1, hh⟩
    exact hx.2 (ContinuousLinearMap.coe_injective hzero)
  · exact measure_iUnion_null (fun j => regular_coordinate_zero_set_null f hf j)

end PlanarNikodym
