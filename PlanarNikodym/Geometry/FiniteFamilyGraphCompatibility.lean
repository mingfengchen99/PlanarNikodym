import PlanarNikodym.Geometry.AnalyticCylindricalPartition
import Mathlib.Topology.Connected.Clopen

/-! On a connected root graph, a finite family with no shared zeros cannot switch
which member vanishes. Thus graph compatibility follows from actual separation. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem finite_family_zero_or_nonzero_on_preconnected
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] {S : Set X}
    (hS : IsPreconnected S) (f : ι → X → ℝ)
    (hf : ∀ i, ContinuousOn (f i) S)
    (hz : ∀ x ∈ S, ∃ i, f i x = 0)
    (hu : ∀ x ∈ S, ∀ i j, f i x = 0 → f j x = 0 → i = j) (i : ι) :
    (∀ x ∈ S, f i x = 0) ∨ (∀ x ∈ S, f i x ≠ 0) := by
  classical
  letI : PreconnectedSpace S := Subtype.preconnectedSpace hS
  let Z : Set S := {x | f i x = 0}
  have hclosed : IsClosed Z := isClosed_eq (hf i).restrict continuous_const
  have he : Z = ⋂ j : {j : ι // j ≠ i}, {x : S | f j x ≠ 0} := by
    ext x
    constructor
    · intro hx
      exact mem_iInter.mpr fun j hj => j.property (hu x x.property j i hj hx)
    · intro hx
      obtain ⟨j, hj⟩ := hz x x.property
      by_cases hji : j = i
      · change f i x = 0
        simpa only [hji] using hj
      · exact False.elim ((mem_iInter.mp hx ⟨j, hji⟩) hj)
  have hopen : IsOpen Z := by
    rw [he]
    exact isOpen_iInter_of_finite fun j => isOpen_ne_fun (hf j).restrict continuous_const
  rcases isClopen_iff.mp (show IsClopen Z from ⟨hclosed, hopen⟩) with h | h
  · right
    intro x hx hz'
    have hxZ : (⟨x, hx⟩ : S) ∈ Z := hz'
    rw [h] at hxZ
    exact hxZ
  · left
    intro x hx
    have hxZ : (⟨x, hx⟩ : S) ∈ Z := by rw [h]; trivial
    exact hxZ

/-- Finite families separated on the actual cylinder automatically have constant
sign on each graph and band once the ordered root graphs cover their zero union. -/
theorem analyticCylindricalCell_separated_family_sign_constant
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    {N : ℕ} {U : Set E} (c : Fin (N + 2) → E → ℝ) (hU : IsConnected U)
    (ha : ∀ i, AnalyticOnNhd ℝ (c i) U)
    (hc : ∀ x ∈ U, StrictMono (fun i => c i x))
    (f : ι → E × ℝ → ℝ)
    (hf : ∀ j, ContinuousOn (f j) (analyticBand U (c 0) (c (Fin.last (N + 1)))))
    (hz : ∀ j z, z ∈ analyticBand U (c 0) (c (Fin.last (N + 1))) → f j z = 0 →
      ∃ l : Fin N, z.2 = c l.castSucc.succ z.1)
    (hg : ∀ l : Fin N, ∀ z ∈ analyticCylindricalCell U c (Sum.inl l),
      ∃ j, f j z = 0)
    (hu : ∀ z ∈ analyticBand U (c 0) (c (Fin.last (N + 1))),
      ∀ i j, f i z = 0 → f j z = 0 → i = j) :
    ∀ (i : Fin N ⊕ Fin (N + 1)) j,
      (∀ z ∈ analyticCylindricalCell U c i, f j z < 0) ∨
      (∀ z ∈ analyticCylindricalCell U c i, f j z = 0) ∨
      (∀ z ∈ analyticCylindricalCell U c i, 0 < f j z) := by
  apply analyticCylindricalCell_family_sign_constant c hU ha hc f hf hz
  intro j l
  exact finite_family_zero_or_nonzero_on_preconnected
    (isConnected_analyticCylindricalCell c hU ha hc (Sum.inl l)).isPreconnected f
    (fun i => (hf i).mono (analyticCylindricalCell_subset c hc (Sum.inl l)))
    (hg l) (fun z hz => hu z (analyticCylindricalCell_subset c hc _ hz)) j

end PlanarNikodym
