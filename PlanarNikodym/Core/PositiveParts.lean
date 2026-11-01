import PlanarNikodym.Core.ReuseBasics
import Mathlib.MeasureTheory.Measure.NullMeasurable

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem HasPositivePart.not_of_null {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {S : Set X} (hS : μ S = 0) : ¬ HasPositivePart μ S := by
  rintro ⟨A, hA, _, hp⟩
  exact hp.ne' (measure_mono_null hA hS)

/-- A countable Borel cover modulo an outer-null set detects positive inner
measure in one of its members. Measurability of the members is essential. -/
theorem HasPositivePart.exists_of_countable_cover {X ι : Type*} [MeasurableSpace X]
    [Countable ι] {μ : Measure X} {S B : Set X} (hS : HasPositivePart μ S)
    (T : ι → Set X) (hT : ∀ i, MeasurableSet (T i))
    (hcover : S ⊆ B ∪ ⋃ i, T i) (hB : μ B = 0) :
    ∃ i, HasPositivePart μ (T i) := by
  classical
  by_contra hn
  have hz : ∀ i, μ (T i) = 0 := by
    intro i
    apply nonpos_iff_eq_zero.mp
    apply not_lt.mp
    intro hp
    exact hn ⟨i, T i, Subset.rfl, hT i, hp⟩
  exact HasPositivePart.not_of_null
    (measure_mono_null hcover (measure_union_null hB (measure_iUnion_null hz))) hS

theorem HasPositivePart.of_nullMeasurable_pos {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {S : Set X} (hS : NullMeasurableSet S μ) (hp : 0 < μ S) :
    HasPositivePart μ S := by
  obtain ⟨A, hAS, hA, he⟩ := hS.exists_measurable_subset_ae_eq
  exact ⟨A, hAS, hA, (measure_congr he).symm ▸ hp⟩

theorem HasPositivePart.exists_of_countable_nullMeasurable_cover {X ι : Type*}
    [MeasurableSpace X] [Countable ι] {μ : Measure X} {S B : Set X}
    (hS : HasPositivePart μ S) (T : ι → Set X) (hT : ∀ i, NullMeasurableSet (T i) μ)
    (hcover : S ⊆ B ∪ ⋃ i, T i) (hB : μ B = 0) :
    ∃ i, HasPositivePart μ (T i) := by
  classical
  by_contra hn
  have hz : ∀ i, μ (T i) = 0 := by
    intro i
    apply nonpos_iff_eq_zero.mp
    apply not_lt.mp
    intro hp
    exact hn ⟨i, HasPositivePart.of_nullMeasurable_pos (hT i) hp⟩
  exact HasPositivePart.not_of_null
    (measure_mono_null hcover (measure_union_null hB (measure_iUnion_null hz))) hS

end PlanarNikodym
