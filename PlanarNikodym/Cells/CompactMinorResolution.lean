import PlanarNikodym.Cells.MinorPatchResolution
import PlanarNikodym.Cells.UniformAuxiliaryJets
import PlanarNikodym.Tame.DefinableAuxiliaryJets

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology

namespace PlanarNikodym

/-- For the actual pair of rank minors, one constructed definable closed
null exceptional set simultaneously gives pointwise lower-dimensional
pieces and a finite auxiliary jet order on every actual compact
parameter set avoiding that exception.

The compact set may be arbitrary; no definability certificate is needed
for it. The conclusion does not give a finite disjoint cell cover. -/
theorem DoubleRankMinor.exists_patch_exception_pieces_and_compact_order {d : ℕ}
    {G : Family 2 (d + 1)} (M : DoubleRankMinor G)
    (hG : G.RanTame) (ho : IsOpen G.W) (hc : IsConnected G.W) (ha : G.IsAnalytic)
    (hM : G.W ⊆ closure M.regularSet)
    {V : Set (Base 2)} {U : Set (Aux (d + 1))}
    (hVd : RanDefinable V) (hUd : RanDefinable U)
    (hoV : IsOpen V) (hoU : IsOpen U) (hcV : IsConnected V) (hcU : IsConnected U)
    (hVU : V ×ˢ U ⊆ G.W) {K : Set (Base 2)}
    (hK : IsCompact K) (hKV : K ⊆ V) (hKd : RanDefinable K) :
    ∃ E : Set (Base 2), RanDefinable E ∧ IsClosed E ∧ volume E = 0 ∧
      (∀ p ∈ K ×ˢ U, p.1 ∉ E → p ∉ M.regularSet →
        ∃ P : AnalyticPiece G, P.dim = d ∧ P.family.RanTame ∧ p ∈ P.image) ∧
      (∀ L : Set (Parameters 2 (d + 1)), IsCompact L → L ⊆ K ×ˢ U →
        (∀ p ∈ L, p.1 ∉ E) →
        ∃ N : ℕ, ∀ p ∈ L, p ∉ M.regularSet →
          ∃ k < N, ∃ (s : Fin k → Fin (d + 1)) (j : Fin (d + 1)),
            auxiliaryJet M.productValue k s p = 0 ∧
              fderiv ℝ (auxiliaryJet M.productValue k s) p (0, Pi.single j 1) ≠ 0) := by
  let F := M.productValue
  have hFa : AnalyticOnNhd ℝ F G.W := M.productValue_analytic ho ha
  have hFn : ∃ p ∈ G.W, F p ≠ 0 := M.productValue_nontrivial hc hM
  have hnonzero := exists_nonzero_on_analytic_product_patch hFa hc.isPreconnected hFn
    hoV hoU hcV.nonempty hcU.nonempty hVU
  have hD := ranDefinable_parameter_product hVd hUd
  have hFd : RanDefinableOn (F ∘ ranParameterEquiv (d + 1))
      (ranParameterEquiv (d + 1) ⁻¹' (V ×ˢ U)) :=
    (M.productValue_definable hG ho ha).restrict hD (fun _ hx => hVU hx)
  obtain ⟨E, hEd, hEc, hEn, hEcover⟩ :=
    exists_ranDefinable_closed_null_flat_fiber_exception hVd hUd hoV hoU hcV hcU
      (hFa.mono hVU) hFd hnonzero hK hKV hKd
  have hnf (p : Parameters 2 (d + 1)) (hp : p ∈ K ×ˢ U) (hpE : p.1 ∉ E) :
      ¬ ∀ᶠ u in 𝓝 p.2, F (p.1, u) = 0 := by
    intro hflat
    have hz : p.1 ∈ K ∩ flatFiberCenters F V U :=
      ⟨hp.1, hKV hp.1, p.2, hp.2, hflat⟩
    exact hpE (hEcover (subset_closure hz))
  have hzero (p : Parameters 2 (d + 1)) (hp : p ∈ K ×ˢ U)
      (hpD : p ∉ M.regularSet) : F p = 0 := by
    by_contra hn
    exact hpD ((M.mem_regularSet_iff_product p).mpr ⟨hVU ⟨hKV hp.1, hp.2⟩, hn⟩)
  refine ⟨E, hEd, hEc, hEn, ?_, ?_⟩
  · intro p hp hpE hpD
    rcases auxiliary_zero_flat_or_lower_piece G ho ha F hFa
        (hVU ⟨hKV hp.1, hp.2⟩) (hzero p hp hpD) with hflat | ⟨P, hd, ht, hpP, _⟩
    · exact (hnf p hp hpE hflat).elim
    · exact ⟨P, hd, ht, hpP⟩
  · intro L hL hLK hLE
    have hLW : L ⊆ G.W := fun p hp => hVU ⟨hKV (hLK hp).1, (hLK hp).2⟩
    obtain ⟨N, hN⟩ := exists_uniform_regular_auxiliaryJet_order ho hFa hL hLW
      (fun p hp => hnf p (hLK hp) (hLE p hp))
    exact ⟨N, fun p hp hpD => hN p hp (hzero p (hLK hp) hpD)⟩

end PlanarNikodym
