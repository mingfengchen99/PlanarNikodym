import PlanarNikodym.Cells.AuxiliaryImplicitCharts
import PlanarNikodym.Tame.DefinableFlatFibers
import PlanarNikodym.Tame.DefinableRankMinors

/-! The actual two rank minors are resolved locally outside a constructed
definable closed null set of centres. Pieces are obtained pointwise; a
finite disjoint compatible cell decomposition is a separate theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory

namespace PlanarNikodym

def DoubleRankMinor.productValue {d : ℕ} {G : Family 2 d} (M : DoubleRankMinor G)
    (p : Parameters 2 d) : ℝ :=
  M.point.value (fun j t p => G.uColumn p j t) p *
    M.curve.value (fun j t p => G.totalColumn p j t) p

theorem DoubleRankMinor.mem_regularSet_iff_product {d : ℕ} {G : Family 2 d}
    (M : DoubleRankMinor G) (p : Parameters 2 d) :
    p ∈ M.regularSet ↔ p ∈ G.W ∧ M.productValue p ≠ 0 := by
  simp only [DoubleRankMinor.regularSet, mem_setOf_eq, DoubleRankMinor.productValue,
    mul_ne_zero_iff]

theorem DoubleRankMinor.productValue_analytic {d : ℕ} {G : Family 2 d}
    (M : DoubleRankMinor G) (ho : IsOpen G.W) (ha : G.IsAnalytic) :
    AnalyticOnNhd ℝ M.productValue G.W :=
  (M.point.analytic _ G.W (G.uColumn_analytic ho ha)).mul
    (M.curve.analytic _ G.W (G.totalColumn_analytic ho ha))

theorem DoubleRankMinor.productValue_definable {d : ℕ} {G : Family 2 d}
    (M : DoubleRankMinor G) (hG : G.RanTame) (ho : IsOpen G.W) (ha : G.IsAnalytic) :
    RanDefinableOn (M.productValue ∘ ranParameterEquiv d)
      (ranParameterEquiv d ⁻¹' G.W) := by
  have hp := M.point.ranDefinableOn hG.1 (hG.uColumn ho ha)
  have hc := M.curve.ranDefinableOn hG.1 (hG.totalColumn ho ha)
  apply ((ranDefinableFun_mul (hp.zeroExtension hG.1) (hc.zeroExtension hG.1)).ranDefinableOn
    hG.1).congr
  intro x hx
  simp only [ranZeroExtension, if_pos hx]
  rfl

theorem DoubleRankMinor.productValue_nontrivial {d : ℕ} {G : Family 2 d}
    (M : DoubleRankMinor G) (hc : IsConnected G.W) (hM : G.W ⊆ closure M.regularSet) :
    ∃ p ∈ G.W, M.productValue p ≠ 0 := by
  have hD : M.regularSet.Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨p, hp⟩ := hc.nonempty
    simpa only [he, closure_empty, mem_empty_iff_false] using hM hp
  obtain ⟨p, hp⟩ := hD
  exact ⟨p, (M.mem_regularSet_iff_product p).mp hp⟩

/-- On each genuine product patch, the flat-fibre exceptional centres of
the actual rank-minor product have a constructed R_an-definable closed
null envelope. Every remaining rank-irregular parameter has a genuine
centre-preserving tame piece of one smaller auxiliary dimension.

The quantifier is pointwise in the parameter. There is no assertion that
the chosen pieces form a finite or disjoint cover. -/
theorem DoubleRankMinor.exists_patch_exception_and_lower_pieces {d : ℕ}
    {G : Family 2 (d + 1)} (M : DoubleRankMinor G)
    (hG : G.RanTame) (ho : IsOpen G.W) (hc : IsConnected G.W) (ha : G.IsAnalytic)
    (hM : G.W ⊆ closure M.regularSet)
    {V : Set (Base 2)} {U : Set (Aux (d + 1))}
    (hVd : RanDefinable V) (hUd : RanDefinable U)
    (hoV : IsOpen V) (hoU : IsOpen U) (hcV : IsConnected V) (hcU : IsConnected U)
    (hVU : V ×ˢ U ⊆ G.W) {K : Set (Base 2)}
    (hK : IsCompact K) (hKV : K ⊆ V) (hKd : RanDefinable K) :
    ∃ E : Set (Base 2), RanDefinable E ∧ IsClosed E ∧ volume E = 0 ∧
      ∀ p ∈ K ×ˢ U, p.1 ∉ E → p ∉ M.regularSet →
        ∃ P : AnalyticPiece G, P.dim = d ∧ P.family.RanTame ∧ p ∈ P.image := by
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
  refine ⟨E, hEd, hEc, hEn, ?_⟩
  intro p hp hpE hpD
  have hpW : p ∈ G.W := hVU ⟨hKV hp.1, hp.2⟩
  have hFzero : F p = 0 := by
    by_contra hn
    exact hpD ((M.mem_regularSet_iff_product p).mpr ⟨hpW, hn⟩)
  rcases auxiliary_zero_flat_or_lower_piece G ho ha F hFa hpW hFzero with
    hflat | ⟨P, hd, ht, hpP, _⟩
  · have hz : p.1 ∈ K ∩ flatFiberCenters F V U :=
      ⟨hp.1, hKV hp.1, p.2, hp.2, hflat⟩
    exact (hpE (hEcover (subset_closure hz))).elim
  · exact ⟨P, hd, ht, hpP⟩

end PlanarNikodym
