import PlanarNikodym.Tame.FamilySemantics
import PlanarNikodym.Tame.DefinableMapOn

noncomputable section
open Set

namespace PlanarNikodym

theorem Family.RanTame.restrictTo {d : ℕ} {G : Family 2 d} (hG : G.RanTame)
    {U : Set (Parameters 2 d)} (hU : RanDefinable (ranParameterEquiv d ⁻¹' U))
    (hUW : U ⊆ G.W) : (G.restrictTo U).RanTame := by
  refine ⟨hU, hG.2.restrict (ranDefinable_timeParameterDomain (G.restrictTo U) hU) ?_⟩
  intro x hx
  exact ⟨hx.1, hUW hx.2⟩

/-- A parameter map is definable on the domain where it is used. The
ambient extension outside that domain is unrestricted. -/
def RanParameterMapOn {d e : ℕ} (Φ : Parameters 2 e → Parameters 2 d)
    (U : Set (Parameters 2 e)) : Prop :=
  ∀ i, RanDefinableOn (fun x => (ranParameterEquiv d).symm (Φ (ranParameterEquiv e x)) i)
    (ranParameterEquiv e ⁻¹' U)

theorem ranParameterMapOn_of_map {d e : ℕ} {Φ : Parameters 2 e → Parameters 2 d}
    {U : Set (Parameters 2 e)}
    (hΦ : RanDefinableMap (fun x => (ranParameterEquiv d).symm (Φ (ranParameterEquiv e x))))
    (hU : RanDefinable (ranParameterEquiv e ⁻¹' U)) : RanParameterMapOn Φ U :=
  fun i => RanDefinableFun.ranDefinableOn (hΦ i) hU

/-- Definable parameter changes preserve the actual curve-graph semantics.
The theorem does not infer analyticity from definability. -/
theorem Family.RanTame.pullback {d e : ℕ} {G : Family 2 d} {H : Family 2 e}
    (hG : G.RanTame) (hW : RanDefinable (ranParameterEquiv e ⁻¹' H.W))
    (Φ : Parameters 2 e → Parameters 2 d) (hΦ : RanParameterMapOn Φ H.W)
    (hm : MapsTo Φ H.W G.W) (hI : H.I = G.I)
    (hγ : ∀ p ∈ H.W, ∀ t ∈ H.I.carrier, H.γ t p = G.γ t (Φ p)) : H.RanTame := by
  let E := ranTimeParameterEquiv e
  let D := ranTimeParameterEquiv d
  let T := E ⁻¹' (H.I.carrier ×ˢ H.W)
  let F : (Option (RanParameterIndex e) → ℝ) → (Option (RanParameterIndex d) → ℝ) :=
    fun x => D.symm ((E x).1, Φ (E x).2)
  have hT : RanDefinable T := ranDefinable_timeParameterDomain H hW
  have hF : ∀ i, RanDefinableOn (fun x => F x i) T := by
    intro i
    cases i with
    | none => exact (ranDefinableFun_coordinate none).ranDefinableOn hT
    | some i =>
      have hproj : RanDefinableMap (fun x : Option (RanParameterIndex e) → ℝ => x ∘ some) :=
        fun j => ranDefinableFun_coordinate (some j)
      apply ((hΦ i).preimage_map hproj).restrict hT
      intro x hx
      exact hx.2
  have hmap : MapsTo F T (D ⁻¹' (G.I.carrier ×ˢ G.W)) := by
    intro x hx
    change D (D.symm ((E x).1, Φ (E x).2)) ∈ G.I.carrier ×ˢ G.W
    rw [D.apply_symm_apply]
    exact ⟨hI ▸ hx.1, hm hx.2⟩
  refine ⟨hW, ((hG.2.comp_on hT hF hmap).congr ?_)⟩
  intro x hx
  change G.γ (D (D.symm ((E x).1, Φ (E x).2))).1
    (D (D.symm ((E x).1, Φ (E x).2))).2 = H.γ (E x).1 (E x).2
  rw [D.apply_symm_apply]
  exact (hγ (E x).2 hx.2 (E x).1 hx.1).symm

/-- In particular, the centre-preserving analytic charts used by the cell
interfaces preserve tame semantics once their actual graphs are definable.
Existence or definability of such charts is not assumed implicitly. -/
theorem AnalyticPiece.ranTame {d : ℕ} {G : Family 2 d} (P : AnalyticPiece G)
    (hG : G.RanTame)
    (hW : RanDefinable (ranParameterEquiv P.dim ⁻¹' P.family.W))
    (hP : RanParameterMapOn P.embed P.family.W) : P.family.RanTame :=
  hG.pullback hW P.embed hP P.maps_to P.interval_eq (by
    intro p hp t ht
    exact P.identity p hp t (P.interval_eq ▸ ht))

end PlanarNikodym
