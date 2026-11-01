import PlanarNikodym.Cells.RankDecomposition
import Mathlib.MeasureTheory.Group.Measure

/-! The bounded-source certificate cannot state the original unbounded
Lemma 5.7. In fact it forces the full center projection to have finite
area, and cannot exist for a family with the whole parameter space as
domain. This is an interface obstruction, independent of curve ranks. -/
noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem RankDecomposition.center_image_volume_lt_top {d : ℕ} {G : Family 2 d}
    (D : RankDecomposition G) : volume (Prod.fst '' G.W) < ⊤ := by
  let U := ⋃ i, Prod.fst '' (D.piece i).family.W
  have hb : Bornology.IsBounded U := Bornology.isBounded_iUnion.mpr (fun i =>
    (ContinuousLinearMap.fst ℝ (Base 2) (Aux (D.piece i).dim)).lipschitz.isBounded_image
      (D.piece i).bounded_domain)
  have hsub : Prod.fst '' G.W ⊆ D.exceptional ∪ U := by
    rintro _ ⟨p, hp, rfl⟩
    rcases D.cover p hp with he | ⟨i, q, hq, hqp⟩
    · exact Or.inl he
    · apply Or.inr
      apply mem_iUnion.mpr
      refine ⟨i, q, hq, ?_⟩
      exact ((D.piece i).keep_center q hq).symm.trans (congrArg Prod.fst hqp)
  calc
    volume (Prod.fst '' G.W) ≤ volume D.exceptional + volume U :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ = volume U := by rw [D.null_exceptional, zero_add]
    _ < ⊤ := hb.measure_lt_top

theorem Family.not_rankDecomposition_of_infinite_center_volume
    {d : ℕ} (G : Family 2 d) (h : volume (Prod.fst '' G.W) = ⊤) :
    ¬ Nonempty (RankDecomposition G) := by
  rintro ⟨D⟩
  have hd := D.center_image_volume_lt_top
  rw [h] at hd
  exact lt_irrefl _ hd

theorem Family.not_rankDecomposition_of_univ_domain
    {d : ℕ} (G : Family 2 d) (h : G.W = univ) :
    ¬ Nonempty (RankDecomposition G) := by
  apply G.not_rankDecomposition_of_infinite_center_volume
  have he : Prod.fst '' G.W = univ := by
    rw [h, image_univ]
    exact range_eq_univ.mpr Prod.fst_surjective
  rw [he]
  exact measure_univ_of_isAddLeftInvariant volume

end PlanarNikodym
