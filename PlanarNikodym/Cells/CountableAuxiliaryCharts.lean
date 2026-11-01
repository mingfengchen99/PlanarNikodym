import PlanarNikodym.Cells.AuxiliaryImplicitCharts
import Mathlib.Topology.Compactness.Lindelof

/-! Countable centre-preserving charts are extracted separately on each
regular auxiliary-jet zero layer. We never regard a high-jet chart as
an open neighborhood in the original zero set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace PlanarNikodym

theorem exists_countable_regular_auxiliary_zero_pieces {d : ℕ}
    (G : Family 2 (d + 1)) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (F : Parameters 2 (d + 1) → ℝ) (hF : AnalyticOnNhd ℝ F G.W)
    (j : Fin (d + 1)) :
    ∃ S : Set (AnalyticPiece G), S.Countable ∧
      (∀ P ∈ S, P.dim = d ∧ P.family.RanTame ∧ P.image ⊆ {p | F p = 0}) ∧
      ∀ p ∈ G.W, F p = 0 → fderiv ℝ F p (0, Pi.single j 1) ≠ 0 →
        ∃ P ∈ S, p ∈ P.image := by
  classical
  let Z : Set (Parameters 2 (d + 1)) :=
    {p | p ∈ G.W ∧ F p = 0 ∧ fderiv ℝ F p (0, Pi.single j 1) ≠ 0}
  have hex (p : Z) : ∃ (P : AnalyticPiece G) (U : Set (Parameters 2 (d + 1))),
      P.dim = d ∧ P.family.RanTame ∧ P.image ⊆ {y | F y = 0} ∧
      IsOpen U ∧ (p : Parameters 2 (d + 1)) ∈ U ∧
      ∀ y ∈ U, F y = 0 → y ∈ P.image := by
    obtain ⟨P, hdim, htame, _, himg, hlocal⟩ :=
      exists_regular_auxiliary_coordinate_zero_piece G ho ha F hF p.property.1
        p.property.2.1 j p.property.2.2
    obtain ⟨U, hUsub, hUo, hpU⟩ := mem_nhds_iff.mp hlocal
    exact ⟨P, U, hdim, htame, himg, hUo, hpU, fun y hy => hUsub hy⟩
  choose P U hdim htame himg hUo hpU hUsub using hex
  obtain ⟨T, hTc, hcover⟩ := (HereditarilyLindelofSpace.isLindelof Z).elim_countable_subcover
    U hUo (by intro p hp; exact mem_iUnion.mpr ⟨⟨p, hp⟩, hpU ⟨p, hp⟩⟩)
  refine ⟨P '' T, hTc.image P, ?_, ?_⟩
  · rintro Q ⟨q, _, rfl⟩
    exact ⟨hdim q, htame q, himg q⟩
  · intro p hp hz hreg
    obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hcover ⟨hp, hz, hreg⟩)
    exact ⟨P q, mem_image_of_mem P hq, hUsub q p hpq hz⟩

/-- The countable union over orders, coordinate words and final
coordinate directions covers every non-flat original zero. Charts are
allowed to lie in a higher derivative zero layer rather than in `{F=0}`. -/
theorem exists_countable_nonflat_auxiliary_zero_pieces {d : ℕ}
    (G : Family 2 (d + 1)) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (F : Parameters 2 (d + 1) → ℝ) (hF : AnalyticOnNhd ℝ F G.W) :
    ∃ S : Set (AnalyticPiece G), S.Countable ∧
      (∀ P ∈ S, P.dim = d ∧ P.family.RanTame ∧
        ∃ (k : ℕ) (s : Fin k → Fin (d + 1)),
          P.image ⊆ {p | auxiliaryJet F k s p = 0}) ∧
      ∀ p ∈ G.W, F p = 0 → (¬ ∀ᶠ u in 𝓝 p.2, F (p.1, u) = 0) →
        ∃ P ∈ S, p ∈ P.image := by
  classical
  have hex (k : ℕ) (s : Fin k → Fin (d + 1)) (j : Fin (d + 1)) :=
    exists_countable_regular_auxiliary_zero_pieces G ho ha (auxiliaryJet F k s)
      (auxiliaryJet_analytic ho hF k s) j
  choose S hSc hS hcover using hex
  let T := ⋃ (k : ℕ) (s : Fin k → Fin (d + 1)) (j : Fin (d + 1)), S k s j
  have hTc : T.Countable := countable_iUnion fun k =>
    countable_iUnion fun s => countable_iUnion fun j => hSc k s j
  refine ⟨T, hTc, ?_, ?_⟩
  · intro P hP
    obtain ⟨k, s, j, hP⟩ := mem_iUnion.mp hP |>.imp fun k h => by
      simpa only [mem_iUnion] using h
    exact ⟨(hS k s j P hP).1, (hS k s j P hP).2.1, k, s, (hS k s j P hP).2.2⟩
  · intro p hp hz hnflat
    rcases auxiliary_zero_flat_or_regularJet ho hF hp hz with hflat | ⟨k, s, j, hzj, hrj⟩
    · exact (hnflat hflat).elim
    · obtain ⟨P, hP, hpP⟩ := hcover k s j p hp hzj hrj
      exact ⟨P, mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨j, hP⟩⟩⟩, hpP⟩

end PlanarNikodym
