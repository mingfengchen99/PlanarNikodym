import PlanarNikodym.Tame.AnalyticSublevelComponentSeeds

/-! Both original AnalyticParameterDomain seed alternatives have actually
finite components and tame component restrictions, with no new input. -/
noncomputable section
open Set Metric
namespace PlanarNikodym

theorem Family.ranTame_components_seed_ball
    {d : ℕ} (G : Family 2 d) (c : Parameters 2 d) (r : ℝ)
    (hW : G.W = ball c r) (ha : G.IsAnalyticAtClosure) :
    (componentDomains G.W).Finite ∧
      ∀ p, (G.restrictTo (connectedComponentIn G.W p)).RanTame := by
  have hG : G.RanTame := G.ranTame_seed_ball c r hW ha
  have hpre : IsPreconnected G.W := hW ▸ (convex_ball c r).isPreconnected
  have hfinite : (componentDomains G.W).Finite := by
    apply components_finite_of_finite_preconnected_cover (fun _ : Unit => G.W)
      (fun _ => hpre) (fun _ => subset_rfl)
    intro x hx
    exact mem_iUnion.mpr ⟨(), hx⟩
  refine ⟨hfinite, ?_⟩
  intro p
  by_cases hp : p ∈ G.W
  · have he := hpre.connectedComponentIn hp
    exact hG.restrictTo (he.symm ▸ hG.1) (connectedComponentIn_subset G.W p)
  · apply hG.restrictTo _ (connectedComponentIn_subset G.W p)
    rw [connectedComponentIn_eq_empty hp, preimage_empty]
    exact Set.definable_empty

/-- The actual ball/sublevel alternatives of the original seed now satisfy
finite components and definable tame component restrictions. This does not
assert the result for an arbitrary first-order R_an formula domain. -/
theorem Family.ranTame_components_seed
    {d : ℕ} (G : Family 2 d) (hD : AnalyticParameterDomain G)
    (ha : G.IsAnalyticAtClosure) :
    (componentDomains G.W).Finite ∧
      ∀ p, (G.restrictTo (connectedComponentIn G.W p)).RanTame := by
  rcases hD with ⟨_, hb, hball | hsub⟩
  · obtain ⟨c, r, _, hW⟩ := hball
    exact G.ranTame_components_seed_ball c r hW ha
  · obtain ⟨f, hf, hW⟩ := hsub
    exact G.ranTame_components_seed_sublevel hb ha f hf hW

end PlanarNikodym
