import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! Completed measurability of descriptive analytic sets.

For each finite Baire prefix we take a measurable envelope of its image.
Outside a countable union of null sets, every point in an envelope has a
successor and belongs to the closure of the corresponding image. A branch
then recovers an actual preimage by continuity. This supplies the measure
theoretic justification for the projected sweeps in §7.3 of the paper.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace PlanarNikodym

/-- A tree with a successor at every occupied node has a Baire branch. The
lists are reversed prefixes, in the convention of `PiNat.res`. -/
theorem exists_baire_branch {P : List ℕ → Prop} (hroot : P [])
    (hchild : ∀ s, P s → ∃ k, P (k :: s)) :
    ∃ a : ℕ → ℕ, ∀ n, P (PiNat.res a n) := by
  classical
  let step : List ℕ → ℕ := fun s => if hs : P s then (hchild s hs).choose else 0
  have hstep (s : List ℕ) (hs : P s) : P (step s :: s) := by
    simpa only [step, dif_pos hs] using (hchild s hs).choose_spec
  let b : ℕ → List ℕ := fun n => (fun s => step s :: s)^[n] []
  let a : ℕ → ℕ := fun n => step (b n)
  have hb (n : ℕ) : b (n + 1) = a n :: b n :=
    Function.iterate_succ_apply' _ n []
  have hres (n : ℕ) : PiNat.res a n = b n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [PiNat.res_succ, ih, hb]
  refine ⟨a, fun n => ?_⟩
  rw [hres]
  induction n with
  | zero => exact hroot
  | succ n ih => rw [hb]; exact hstep _ ih

/-- Continuity identifies a point lying in the closures of every image
cylinder along a fixed Baire branch. No compactness of the image is used. -/
theorem eq_of_mem_closure_baire_cylinders {X : Type*} [TopologicalSpace X] [T2Space X]
    {f : (ℕ → ℕ) → X} (hf : Continuous f) (a : ℕ → ℕ) {x : X}
    (hx : ∀ n, x ∈ closure (f '' PiNat.cylinder a n)) : x = f a := by
  by_contra hne
  obtain ⟨U, V, hU, hV, hxU, haV, hUV⟩ := t2_separation hne
  obtain ⟨W, ⟨b, n, rfl⟩, ha, hW⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ => ℕ)).exists_subset_of_mem_open
      haV (hV.preimage hf)
  have hcyl : PiNat.cylinder a n = PiNat.cylinder b n :=
    PiNat.mem_cylinder_iff_eq.mp ha
  obtain ⟨y, hyU, z, hz, rfl⟩ := mem_closure_iff.mp (hx n) U hU hxU
  rw [hcyl] at hz
  exact Set.disjoint_left.mp hUV hyU (hW hz)

/-- An s-finite measurable envelope is almost everywhere contained in
every measurable superset of the original set. -/
theorem toMeasurable_ae_subset_of_subset {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {A B : Set X}
    (hB : MeasurableSet B) (hAB : A ⊆ B) : toMeasurable μ A ≤ᵐ[μ] B := by
  apply ae_le_set.mpr
  rw [sdiff_eq, Measure.measure_toMeasurable_inter_of_sFinite hB.compl A]
  have he : A ∩ Bᶜ = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false,
      not_and]
    exact fun hx => not_not.mpr (hAB hx)
  rw [he, measure_empty]

/-- A continuous image of Baire space is measurable in the completion
of every s-finite Borel measure on a Hausdorff target. -/
theorem nullMeasurableSet_range_of_continuous_baire {X : Type*}
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : (ℕ → ℕ) → X} (hf : Continuous f) :
    NullMeasurableSet (range f) μ := by
  let A : List ℕ → Set X := fun s => f '' {a | PiNat.res a s.length = s}
  let H : List ℕ → Set X := fun s => toMeasurable μ (A s)
  have hA (s : List ℕ) : A s = ⋃ k, A (k :: s) := by
    have hp : {a : ℕ → ℕ | PiNat.res a s.length = s} =
        ⋃ k, {a : ℕ → ℕ | PiNat.res a (k :: s).length = k :: s} := by
      ext a
      simp only [mem_setOf_eq, mem_iUnion, List.length_cons, PiNat.res_succ,
        List.cons.injEq]
      exact ⟨fun h => ⟨a s.length, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
    exact (congrArg (fun S => f '' S) hp).trans image_iUnion
  have hchild (s : List ℕ) : H s ≤ᵐ[μ] ⋃ k, H (k :: s) := by
    apply toMeasurable_ae_subset_of_subset μ
      (MeasurableSet.iUnion fun k => measurableSet_toMeasurable μ (A (k :: s)))
    rw [hA]
    exact iUnion_mono fun k => subset_toMeasurable μ (A (k :: s))
  have hclosed (s : List ℕ) : H s ≤ᵐ[μ] closure (A s) :=
    toMeasurable_ae_subset_of_subset μ isClosed_closure.measurableSet subset_closure
  have hH : H [] ≤ᵐ[μ] range f := by
    filter_upwards [ae_all_iff.mpr hchild, ae_all_iff.mpr hclosed] with x hx hc
    intro hx0
    obtain ⟨a, ha⟩ := exists_baire_branch hx0 (fun s hs => mem_iUnion.mp (hx s hs))
    refine ⟨a, (eq_of_mem_closure_baire_cylinders hf a (x := x) ?_).symm⟩
    intro n
    have hn := hc (PiNat.res a n) (ha n)
    change x ∈ closure (A (PiNat.res a n)) at hn
    rw [PiNat.cylinder_eq_res]
    simpa only [A, PiNat.res_length] using hn
  have hroot : A [] = range f := by simp [A]
  refine ⟨H [], measurableSet_toMeasurable μ (A []), ?_⟩
  filter_upwards [hH] with x hx
  exact propext ⟨fun h => subset_toMeasurable μ (A []) (hroot.symm ▸ h), hx⟩

/-- Descriptive analytic sets are universally measurable for s-finite
measures whose measurable sets include the opens. This asserts completed
measurability, and does not assert that analytic sets are Borel. -/
theorem analyticSet_nullMeasurableSet {X : Type*}
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {S : Set X} (hS : AnalyticSet S) (μ : Measure X) [SFinite μ] :
    NullMeasurableSet S μ := by
  rw [AnalyticSet] at hS
  rcases hS with rfl | ⟨f, hf, rfl⟩
  · exact nullMeasurableSet_empty
  · exact nullMeasurableSet_range_of_continuous_baire μ hf

end PlanarNikodym
