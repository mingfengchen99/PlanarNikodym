import PlanarNikodym.Projection.DyadicBlindTreeBudget

/-! A single positive thickening for an actual finite blind trace.

The shrinking branch bound uses half of each good ancestor tube's width.
Finiteness and positivity of all actual node lengths provide one remaining
radius for every descendant and every parameter value simultaneously.
-/

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal BigOperators

namespace PlanarNikodym

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace FiniteBlindFamily

/-- A closed thickening of a finite segment union is precisely the union
of the equally thickened segments. Compactness supplies nearest points. -/
theorem cthickening_carrier_eq (P : FiniteBlindFamily E) (v : E)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    cthickening δ (P.carrier v) =
      ⋃ j, cthickening δ (centeredBlindSegment (P.center j) v (P.halfLength j)) := by
  apply Subset.antisymm
  · rw [(P.isCompact_carrier v).cthickening_eq_biUnion_closedBall hδ]
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨j, closedBall_subset_cthickening hj δ hxy⟩
  · apply iUnion_subset
    intro j
    exact cthickening_subset_of_subset δ (subset_iUnion (fun j =>
      centeredBlindSegment (P.center j) v (P.halfLength j)) j)

end FiniteBlindFamily

namespace DyadicBlindTrace

variable {P₀ : FiniteBlindFamily E} {v : ℕ → E} {Λ : ℕ → ℝ}

/-- The full relative tube used by the nonlinear projection estimate. -/
def fullNodeTube {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (η : ℝ) (u : trace.Node) : Set E :=
  thinSegmentTube (trace.nodeCenter u) (v (trace.nodeLevel u))
    (2 * trace.nodeHalfLength u) (η * (2 * trace.nodeHalfLength u))

/-- Reserving half the tube width accommodates the same positive
thickening of every terminal descendant. -/
theorem thickened_terminal_subset_fullNodeTube {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q)
    (hP₀ : ∀ i, 0 < P₀.halfLength i) (hΛ : ∀ k < n, 0 < Λ k)
    {β V η δ : ℝ} (hs : trace.Shrinks β) (hβ : 0 ≤ β) (hβhalf : β ≤ 1 / 2)
    (hV : 0 ≤ V) (hv : ∀ k ≤ n, ‖v k‖ ≤ V)
    (hmargin : V * β ≤ η / 2) (hδ : 0 ≤ δ)
    (hsmall : ∀ u : trace.Node, δ ≤ η * trace.nodeHalfLength u)
    (u : trace.Node) (j : Q.Index) (huj : trace.Descends u j) :
    cthickening δ (centeredBlindSegment (Q.center j) (v n) (Q.halfLength j)) ⊆
      trace.fullNodeTube η u := by
  have hsub := trace.terminalSegment_subset_nodeTube hP₀ hΛ hs hβ hβhalf hV hv u j huj
  have hthick := cthickening_subset_blind_tube
    (isCompact_centeredBlindSegment (Q.center j) (v n) (Q.halfLength j)) hδ hsub
  have ha : 0 ≤ trace.nodeHalfLength u := (trace.nodeHalfLength_pos hP₀ hΛ u).le
  have hwidth : 2 * V * β * trace.nodeHalfLength u + δ ≤
      η * (2 * trace.nodeHalfLength u) := by
    have hm := mul_le_mul_of_nonneg_right hmargin ha
    have hd := hsmall u
    nlinarith
  intro x hx
  obtain ⟨t, z, ht, hz, he⟩ := hthick hx
  exact ⟨t, z, ht, hz.trans hwidth, he⟩

/-- One geometric thickness works for all nodes and all descendants,
while remaining inside the prescribed open container. -/
theorem exists_thickening_subset_fullNodeTubes [ProperSpace E]
    {n : ℕ} {Q : FiniteBlindFamily E} (trace : DyadicBlindTrace P₀ v Λ n Q)
    (hP₀ : ∀ i, 0 < P₀.halfLength i) (hΛ : ∀ k < n, 0 < Λ k)
    {β V η : ℝ} (hs : trace.Shrinks β) (hβ : 0 ≤ β) (hβhalf : β ≤ 1 / 2)
    (hV : 0 ≤ V) (hv : ∀ k ≤ n, ‖v k‖ ≤ V) (hη : 0 < η)
    (hmargin : V * β ≤ η / 2)
    {W : Set E} (hW : IsOpen W) (hQW : Q.carrier (v n) ⊆ W) :
    ∃ δ > 0,
      IsCompact (cthickening δ (Q.carrier (v n))) ∧
      Q.carrier (v n) ⊆ interior (cthickening δ (Q.carrier (v n))) ∧
      cthickening δ (Q.carrier (v n)) ⊆ W ∧
      ∀ (u : trace.Node) (j : Q.Index), trace.Descends u j →
        cthickening δ (centeredBlindSegment (Q.center j) (v n) (Q.halfLength j)) ⊆
          trace.fullNodeTube η u := by
  obtain ⟨ρ, hρ, hρall⟩ := trace.exists_uniform_node_radius hP₀ hΛ hη
  obtain ⟨δ, hδ, hδρ, hcompact, hinterior, hinside⟩ :=
    exists_compact_blind_thickening (Q.isCompact_carrier (v n)) hW hQW hρ
  refine ⟨δ, hδ, hcompact, hinterior, hinside, ?_⟩
  intro u j huj
  exact trace.thickened_terminal_subset_fullNodeTube hP₀ hΛ hs hβ hβhalf hV hv
    hmargin hδ.le (fun a => hδρ.trans (hρall a).le) u j huj

/-- Uniform simultaneous projection bound after a positive thickening.
The single radius depends on the actual finite trace, not on the tested
parameter or its choice of good ancestor. -/
theorem exists_uniform_thickened_projection_bound [ProperSpace E]
    {ι : Type*} {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q)
    (hP₀ : ∀ i, 0 < P₀.halfLength i)
    (hΛ : ∀ k < n, 1 ≤ Λ k) (hvne : ∀ k < n, v k ≠ 0)
    {β V η : ℝ} (hs : trace.Shrinks β) (hβ : 0 ≤ β) (hβhalf : β ≤ 1 / 2)
    (hV : 0 ≤ V) (hv : ∀ k ≤ n, ‖v k‖ ≤ V) (hη : 0 < η)
    (hmargin : V * β ≤ η / 2)
    {W : Set E} (hW : IsOpen W) (hQW : Q.carrier (v n) ⊆ W)
    (f : ι → E → ℝ) (A : Set ι) (ε : ℝ≥0∞) (good : ι → trace.Node → Prop)
    (hmeasure : ∀ t ∈ A, ∀ u, good t u →
      volume (f t '' trace.fullNodeTube η u) ≤ ε * ENNReal.ofReal (2 * trace.nodeHalfLength u))
    (hbranch : ∀ t ∈ A, trace.EveryBranchMarked (good t)) :
    ∃ δ > 0,
      IsCompact (cthickening δ (Q.carrier (v n))) ∧
      Q.carrier (v n) ⊆ interior (cthickening δ (Q.carrier (v n))) ∧
      cthickening δ (Q.carrier (v n)) ⊆ W ∧
      ∀ t ∈ A, volume (f t '' cthickening δ (Q.carrier (v n))) ≤
        ε * ENNReal.ofReal (2 * Q.budget) := by
  obtain ⟨δ, hδ, hcompact, hinterior, hinside, hcover⟩ :=
    trace.exists_thickening_subset_fullNodeTubes hP₀
      (fun k hk => lt_of_lt_of_le zero_lt_one (hΛ k hk)) hs hβ hβhalf hV hv hη hmargin hW hQW
  refine ⟨δ, hδ, hcompact, hinterior, hinside, ?_⟩
  intro t ht
  rw [Q.cthickening_carrier_eq (v n) hδ.le, image_iUnion]
  apply trace.volume_terminalUnion_le hP₀ hΛ hvne ε (good t) _ _ (hbranch t ht)
  intro u hu
  apply le_trans (measure_mono ?_) (hmeasure t ht u hu)
  intro x hx
  obtain ⟨j, hju, hxj⟩ := (trace.mem_descendantUnion_iff _ u x).mp hx
  exact image_mono (hcover u j hju) hxj

end DyadicBlindTrace
end PlanarNikodym
