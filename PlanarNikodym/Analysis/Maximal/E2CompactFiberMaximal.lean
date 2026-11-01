import PlanarNikodym.Analysis.Maximal.MaximalMeasurability

/-! Pointwise suprema over compact parameter fibers are upper
semicontinuous, including fibers that become empty at the boundary. -/
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace PlanarNikodym

theorem e2_upperSemicontinuous_compact_fiber_sup
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    (K : Set (X × Y)) (hK : IsCompact K) (F : X × Y → ℝ≥0∞)
    (hF : ContinuousOn F K) :
    UpperSemicontinuous (fun x => ⨆ y, ⨆ (_ : (x, y) ∈ K), F (x, y)) := by
  intro x a ha
  obtain ⟨b, hxb, hba⟩ := exists_between ha
  let B := K ∩ F ⁻¹' Ici b
  have hB : IsCompact B := hK.of_isClosed_subset
    (hF.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici) inter_subset_left
  have hx : x ∉ Prod.fst '' B := by
    rintro ⟨⟨z, y⟩, ⟨hzy, hb⟩, hzx⟩
    change z = x at hzx
    subst z
    have hf : F (x, y) ≤ ⨆ y, ⨆ (_ : (x, y) ∈ K), F (x, y) :=
      le_iSup_of_le y (le_iSup_of_le hzy le_rfl)
    exact (not_le_of_gt hxb) (hb.trans hf)
  filter_upwards [((hB.image continuous_fst).isClosed.isOpen_compl.mem_nhds hx)] with z hz
  apply lt_of_le_of_lt _ hba
  apply iSup_le
  intro y
  apply iSup_le
  intro hzy
  exact le_of_lt (lt_of_not_ge (fun hb => hz ⟨(z, y), ⟨hzy, hb⟩, rfl⟩))

end PlanarNikodym
