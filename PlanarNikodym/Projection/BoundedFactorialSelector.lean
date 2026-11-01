import PlanarNikodym.Projection.FactorialExpansion
import PlanarNikodym.Projection.FactorialSelectorGraph
import PlanarNikodym.Projection.FactorialCoefficientSchedule
import Mathlib.MeasureTheory.Function.Floor

/-! A concrete bounded factorial selector and its compact symbolic graph.

The selector, graph, full parameter projection, and Borel measurability
are constructed here. Nullity of the nonlinear projections still needs
the Taylor error and factorial covering argument; no null-set conclusion
is asserted in this module. -/

noncomputable section
open Set Filter Finset MeasureTheory
open scoped Topology Nat
namespace PlanarNikodym.Wisewell

def boundedFactorialGraph (M : ℝ) : Set Plane :=
  factorialSeriesGraph (boundedCoefficientSchedule M)

/-- A genuine function of the real parameter, using greedy factorial
digits except for the right endpoint of the unit interval. -/
def boundedFactorialChoice (M y : ℝ) : ℝ :=
  if y = 1 then factorialSelector (boundedCoefficientSchedule M) maximalFactorialDigits
  else factorialSelector (boundedCoefficientSchedule M) (greedyFactorialDigits y)

theorem measurable_greedyFactorialDigits : Measurable greedyFactorialDigits := by
  apply measurable_pi_lambda
  intro n
  let g : ℕ → Fin (n + 2) := fun k => ⟨k % (n + 2), Nat.mod_lt _ (by omega)⟩
  exact (measurable_of_countable g).comp
    ((measurable_const.mul measurable_id).nat_floor)

theorem measurable_boundedFactorialChoice (M : ℝ) (hM : 0 ≤ M) :
    Measurable (boundedFactorialChoice M) := by
  have hs := (continuous_factorialSelector_of_bounded (boundedCoefficientSchedule M) M hM
    (boundedCoefficientSchedule_norm_le M hM)).measurable.comp measurable_greedyFactorialDigits
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const hs

theorem norm_boundedFactorialChoice_le (M : ℝ) (hM : 0 ≤ M) (y : ℝ) :
    ‖boundedFactorialChoice M y‖ ≤ M := by
  unfold boundedFactorialChoice
  split_ifs <;> exact norm_factorialSelector_le_of_bounded
    (boundedCoefficientSchedule M) M hM (boundedCoefficientSchedule_norm_le M hM) _

theorem boundedFactorialChoice_mem_graph (M y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
    (y, boundedFactorialChoice M y) ∈ boundedFactorialGraph M := by
  unfold boundedFactorialChoice
  split_ifs with h
  · subst y
    exact ⟨maximalFactorialDigits, mem_univ _,
      Prod.ext factorialValue_maximalFactorialDigits rfl⟩
  · exact ⟨greedyFactorialDigits y, mem_univ _,
      Prod.ext (factorialValue_greedyFactorialDigits hy.1 (lt_of_le_of_ne hy.2 h)) rfl⟩

theorem isCompact_boundedFactorialGraph (M : ℝ) (hM : 0 ≤ M) :
    IsCompact (boundedFactorialGraph M) :=
  isCompact_factorialSeriesGraph_of_bounded (boundedCoefficientSchedule M) M hM
    (boundedCoefficientSchedule_norm_le M hM)

theorem measurableSet_boundedFactorialGraph (M : ℝ) (hM : 0 ≤ M) :
    MeasurableSet (boundedFactorialGraph M) :=
  (isCompact_boundedFactorialGraph M hM).measurableSet

theorem boundedFactorialGraph_subset (M : ℝ) (hM : 0 ≤ M) :
    boundedFactorialGraph M ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-M) M := by
  rintro p ⟨a, _, rfl⟩
  refine ⟨factorialValue_mem_Icc a, ?_⟩
  have h := norm_factorialSelector_le_of_bounded (boundedCoefficientSchedule M) M hM
    (boundedCoefficientSchedule_norm_le M hM) a
  exact abs_le.mp h

/-- Every unit-interval parameter has an actual selected point on the
compact graph. In particular the first projection is the full interval. -/
theorem fst_image_boundedFactorialGraph (M : ℝ) :
    Prod.fst '' boundedFactorialGraph M = Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, ⟨a, _, rfl⟩, rfl⟩
    exact factorialValue_mem_Icc a
  · intro y hy
    exact ⟨(y, boundedFactorialChoice M y), boundedFactorialChoice_mem_graph M y hy, rfl⟩

def boundedFactorialSweep (M : ℝ) (f : ℝ × Plane → ℝ) (K : Set ℝ) : Set Plane :=
  factorialSeriesSweep (boundedCoefficientSchedule M) f K

theorem isCompact_boundedFactorialSweep (M : ℝ) (hM : 0 ≤ M)
    (f : ℝ × Plane → ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hf : ContinuousOn f (K ×ˢ boundedFactorialGraph M)) :
    IsCompact (boundedFactorialSweep M f K) :=
  isCompact_factorialSeriesSweep_of_bounded (boundedCoefficientSchedule M) M hM
    (boundedCoefficientSchedule_norm_le M hM) f K hK hf

/-- The actual selector chooses one entire curve for every parameter in
the unit interval, all lying in the same compact symbolic sweep. -/
theorem boundedFactorialChoice_curve_subset_sweep (M y : ℝ)
    (hy : y ∈ Icc (0 : ℝ) 1) (f : ℝ × Plane → ℝ) (K : Set ℝ) :
    (fun t => (t, f (t, (y, boundedFactorialChoice M y)))) '' K ⊆
      boundedFactorialSweep M f K := by
  rintro p ⟨t, ht, rfl⟩
  exact ⟨(t, (y, boundedFactorialChoice M y)),
    ⟨ht, boundedFactorialChoice_mem_graph M y hy⟩, rfl⟩

end PlanarNikodym.Wisewell
