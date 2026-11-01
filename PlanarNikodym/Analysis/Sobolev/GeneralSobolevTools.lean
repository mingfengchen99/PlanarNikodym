import PlanarNikodym.Analysis.Sobolev.SobolevAuxTwo
import Mathlib.MeasureTheory.Function.LpSeminorm.Count

/-! Coordinate restriction, actual derivative bounds and finite mixed-norm
sums used in the dimension induction for scaled Sobolev estimates. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace PlanarNikodym

def auxConsLinear (d : ℕ) : ℝ × Aux d →L[ℝ] Aux (d + 1) :=
  ContinuousLinearMap.pi (Fin.cases (ContinuousLinearMap.fst ℝ ℝ (Aux d))
    (fun i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Aux d))))

@[simp] theorem auxConsLinear_apply (d : ℕ) (q : ℝ × Aux d) :
    auxConsLinear d q = Fin.cons q.1 q.2 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem auxConsLinear_measurePreserving (d : ℕ) :
    MeasurePreserving (auxConsLinear d) (volume.prod volume) volume := by
  have he : MeasurePreserving (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (d + 1) => ℝ) 0).symm
      (volume : Measure (ℝ × Aux d)) (volume : Measure (Aux (d + 1))) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm _
  have heq : (auxConsLinear d : ℝ × Aux d → Aux (d + 1)) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm := by
    funext q
    rw [auxConsLinear_apply]
    change Fin.cons q.1 q.2 = Fin.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 q.1 q.2
    exact (Fin.insertNth_zero' q.1 q.2).symm
  rw [heq]
  exact he

def auxTailLinear (d : ℕ) : Aux d →L[ℝ] Aux (d + 1) :=
  (auxConsLinear d).comp (ContinuousLinearMap.inr ℝ ℝ (Aux d))

@[simp] theorem auxTailLinear_apply (d : ℕ) (u : Aux d) :
    auxTailLinear d u = Fin.cons 0 u := by simp [auxTailLinear]

theorem auxTailLinear_norm_le_one (d : ℕ) : ‖auxTailLinear d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using norm_le_pi_norm u j

theorem contDiff_cons_slice {d : ℕ} {F : Aux (d + 1) → ℂ}
    (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    ContDiff ℝ ∞ (fun u : Aux d => F (Fin.cons t u)) := by
  simpa only [Function.comp_def, auxConsLinear_apply, id_eq] using hF.comp ((auxConsLinear d).contDiff.comp
    ((contDiff_const (c := t)).prodMk contDiff_id))

/-- Restricting to a coordinate slice contracts every full derivative norm. -/
theorem norm_iteratedFDeriv_cons_slice_le {d : ℕ} {F : Aux (d + 1) → ℂ}
    (hF : ContDiff ℝ ∞ F) (t : ℝ) (u : Aux d) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun v : Aux d => F (Fin.cons t v)) u‖ ≤
      ‖iteratedFDeriv ℝ j F (Fin.cons t u)‖ := by
  let a : Aux (d + 1) := Fin.cons t 0
  have heq (v : Aux d) : a + auxTailLinear d v = Fin.cons t v := by
    ext i
    refine Fin.cases ?_ (fun k => ?_) i <;> simp [a]
  have hshift : ContDiff ℝ j (fun x => F (a + x)) :=
    contDiff_infty.mp (hF.comp (contDiff_const.add contDiff_id)) j
  have hcomp := (auxTailLinear d).iteratedFDeriv_comp_right hshift u le_rfl
  simp only [Function.comp_def, heq, iteratedFDeriv_comp_add_left] at hcomp
  rw [hcomp]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j F (Fin.cons t u)‖ * ∏ _i : Fin j, ‖auxTailLinear d‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ j F (Fin.cons t u)‖ * 1 := by
      gcongr
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => auxTailLinear_norm_le_one d)
    _ = _ := mul_one _

def auxHeadDerivative {d : ℕ} (F : Aux (d + 1) → ℂ) : Aux (d + 1) → ℂ :=
  fun u => fderiv ℝ F u (Pi.single 0 1)

theorem contDiff_auxHeadDerivative {d : ℕ} {F : Aux (d + 1) → ℂ}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (auxHeadDerivative F) :=
  (contDiff_infty_iff_fderiv.mp hF).2.clm_apply contDiff_const

theorem norm_iteratedFDeriv_auxHeadDerivative_le {d : ℕ} {F : Aux (d + 1) → ℂ}
    (hF : ContDiff ℝ ∞ F) (j : ℕ) (u : Aux (d + 1)) :
    ‖iteratedFDeriv ℝ j (auxHeadDerivative F) u‖ ≤ ‖iteratedFDeriv ℝ (j + 1) F u‖ := by
  have hD := contDiff_infty.mp (contDiff_infty_iff_fderiv.mp hF).2 j
  have h := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ F)
    (c := (Pi.single 0 1 : Aux (d + 1))) (x := u) hD.contDiffAt le_rfl
  change ‖iteratedFDeriv ℝ j (fun y : Aux (d + 1) => fderiv ℝ F y (Pi.single 0 1)) u‖ ≤ _
  simpa only [Pi.norm_single, norm_one, one_mul, norm_iteratedFDeriv_fderiv] using h

theorem deriv_cons_head {d : ℕ} {F : Aux (d + 1) → ℂ}
    (hF : ContDiff ℝ ∞ F) (t : ℝ) (u : Aux d) :
    deriv (fun s : ℝ => F (Fin.cons s u)) t = auxHeadDerivative F (Fin.cons t u) := by
  have hcons : HasDerivAt (fun s : ℝ => (Fin.cons s u : Aux (d + 1)))
      (Pi.single 0 1 : Aux (d + 1)) t := by
    have hv : (Fin.cons 1 (0 : Aux d) : Aux (d + 1)) = Pi.single 0 1 := by
      ext i
      refine Fin.cases ?_ (fun k => ?_) i <;> simp
    have h := (auxConsLinear d).hasFDerivAt.comp_hasDerivAt t
      ((hasFDerivAt_id t).prodMk (hasFDerivAt_const u t)).hasDerivAt
    simpa only [Function.comp_def, auxConsLinear_apply, hv, id_eq,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply,
      one_smul] using h
  exact ((hF.differentiable (by simp) (Fin.cons t u)).hasFDerivAt.comp_hasDerivAt t hcons).deriv

/-- A finite weighted sum of fibre norms can be integrated without requiring
the function on the left to be measurable. -/
theorem eLpNorm_le_weighted_fiber_sum
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    {s : Finset ℕ} {J : ℕ → X × Y → ℝ} (hJ : ∀ j ∈ s, Measurable (J j))
    {M : X → ℝ≥0∞} (C : ℝ≥0∞) (a : ℕ → ℝ≥0∞)
    (p : ℝ≥0) (hp : 1 ≤ p)
    (hM : ∀ x, M x ≤ C * ∑ j ∈ s, a j * eLpNorm (fun y => J j (x, y)) p ν) :
    eLpNorm M p μ ≤ C * ∑ j ∈ s, a j * eLpNorm (J j) p (μ.prod ν) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  let N : ℕ → X → ℝ≥0∞ := fun j x => eLpNorm (fun y => J j (x, y)) p ν
  have hN (j : ℕ) (hj : j ∈ s) : Measurable (N j) :=
    measurable_real_fiber_eLpNorm ν (hJ j hj) p hp0
  have hsum : Measurable (fun x => ∑ j ∈ s, a j * N j x) :=
    Finset.measurable_sum s (fun j hj => measurable_const.mul (hN j hj))
  calc
    _ ≤ eLpNorm (fun x => C * ∑ j ∈ s, a j * N j x) p μ :=
      eLpNorm_mono_enorm (fun x => by simpa only [enorm_eq_self] using hM x)
    _ = C * eLpNorm (fun x => ∑ j ∈ s, a j * N j x) p μ :=
      eLpNorm_ennreal_const_mul μ hsum p hp0 C
    _ ≤ C * ∑ j ∈ s, eLpNorm (fun x => a j * N j x) p μ := by
      gcongr
      have heq : (∑ j ∈ s, fun x => a j * N j x) = (fun x => ∑ j ∈ s, a j * N j x) := by
        funext x
        simp
      rw [← heq]
      exact eLpNorm_sum_le (μ := μ) (p := (p : ℝ≥0∞)) (s := s) (f := fun j x => a j * N j x)
        (fun j hj => (measurable_const.mul (hN j hj)).stronglyMeasurable.aestronglyMeasurable)
        (by exact_mod_cast hp)
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [eLpNorm_ennreal_const_mul μ (hN j hj) p hp0]
      rw [eLpNorm_real_fiber_eLpNorm μ ν (hJ j hj) p hp0]

end PlanarNikodym
