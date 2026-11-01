import PlanarNikodym.Geometry.PolynomialThomFrontier
import PlanarNikodym.Geometry.WeierstrassRootBounds
import Mathlib.Topology.Maps.Proper.Basic

/-! Compact vertical sections for actual polynomial sign cells. The bounded
section is constructed from root bounds, including the two unbounded cells. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym

theorem mem_closure_inter_of_isOpen {E : Type*} [TopologicalSpace E]
    {C U : Set E} {x : E} (hx : x ∈ closure C) (hU : IsOpen U) (hxU : x ∈ U) :
    x ∈ closure (C ∩ U) := by
  apply mem_closure_iff.mpr
  intro O hO hxO
  obtain ⟨y, hyO, hyC⟩ := mem_closure_iff.mp hx (O ∩ U) (hO.inter hU) ⟨hxO, hxU⟩
  exact ⟨y, hyO.1, hyC, hyO.2⟩

/-- A locally compact vertical section puts an actual point of the closure
above every point of the closure of the base. -/
theorem exists_mem_closure_fiber_of_compact_section
    {E T : Type*} [TopologicalSpace E] [TopologicalSpace T]
    (A : Set (E × T)) (C : Set E) (x : E) (K : Set T)
    (hK : IsCompact K) (hx : x ∈ closure C)
    (hsection : ∀ y ∈ C, ∃ t ∈ K, (y, t) ∈ A) :
    ∃ t ∈ K, (x, t) ∈ closure A := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let B : Set (E × K) := {z | (z.1, (z.2 : T)) ∈ closure A}
  have hB : IsClosed B := isClosed_closure.preimage
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hp : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  have hsub : C ⊆ Prod.fst '' B := by
    intro y hy
    obtain ⟨t, htK, htA⟩ := hsection y hy
    exact ⟨(y, ⟨t, htK⟩), subset_closure htA, rfl⟩
  obtain ⟨⟨y, t⟩, ht, hxy⟩ := closure_minimal hsub hp hx
  exact ⟨t, t.property, hxy ▸ ht⟩

theorem oneDimensionalSign_eq_on_of_isPreconnected
    {S : Set ℝ} (hS : IsPreconnected S) (f : ℝ → ℝ)
    (hf : ContinuousOn f S) (hn : ∀ x ∈ S, f x ≠ 0)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) :
    oneDimensionalSign (f a) = oneDimensionalSign (f b) := by
  rcases hS.mapsTo_Ioi_or_Iio hf hn with hp | hm
  · rw [oneDimensionalSign_eq_two.mpr (hp ha), oneDimensionalSign_eq_two.mpr (hp hb)]
  · rw [oneDimensionalSign_eq_zero.mpr (hm ha), oneDimensionalSign_eq_zero.mpr (hm hb)]

/-- Every nonempty polynomial sign fiber has a point in a fixed compact
interval once all roots of its nonzero members lie in a fixed interval. -/
theorem polynomial_sign_cell_exists_bounded_point {ι : Type*}
    (P : ι → ℝ[X]) (s : ι → Fin 3) (R : ℝ) (hR : 0 < R)
    (hbound : ∀ j, P j ≠ 0 → ∀ t, (P j).eval t = 0 → |t| < R)
    (hne : (polynomialThomFamilyCell false P s).Nonempty) :
    ∃ t ∈ Icc (-(R + 1)) (R + 1), t ∈ polynomialThomFamilyCell false P s := by
  obtain ⟨t, ht⟩ := hne
  by_cases hl : -(R + 1) ≤ t
  · by_cases hu : t ≤ R + 1
    · exact ⟨t, ⟨hl, hu⟩, ht⟩
    · have hRt : R < t := by linarith
      refine ⟨R + 1, ⟨by linarith, le_rfl⟩, fun j => ?_⟩
      change oneDimensionalSign ((P j).eval (R + 1)) = s j
      by_cases hj : P j = 0
      · simpa only [hj, eval_zero, polynomialSignCondition, Bool.false_eq_true, ite_false] using ht j
      · have hn (u : ℝ) (hu : u ∈ Ioi R) : (P j).eval u ≠ 0 := by
          intro he
          have hb := (abs_lt.mp (hbound j hj u he)).2
          exact (not_lt_of_ge hu.le) hb
        exact (oneDimensionalSign_eq_on_of_isPreconnected isPreconnected_Ioi
          (P j).eval (P j).continuous.continuousOn hn (by simp) hRt).trans (ht j)
  · have htR : t < -R := by linarith
    refine ⟨-(R + 1), ⟨le_rfl, by linarith⟩, fun j => ?_⟩
    change oneDimensionalSign ((P j).eval (-(R + 1))) = s j
    by_cases hj : P j = 0
    · simpa only [hj, eval_zero, polynomialSignCondition, Bool.false_eq_true, ite_false] using ht j
    · have hn (u : ℝ) (hu : u ∈ Iio (-R)) : (P j).eval u ≠ 0 := by
        intro he
        have hb := (abs_lt.mp (hbound j hj u he)).1
        exact (not_lt_of_ge hu.le) hb
      exact (oneDimensionalSign_eq_on_of_isPreconnected isPreconnected_Iio
        (P j).eval (P j).continuous.continuousOn hn (by simp) htR).trans (ht j)

end PlanarNikodym
