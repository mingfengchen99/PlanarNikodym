import PlanarNikodym.Geometry.Cinematic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Separation.Regular

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold
namespace PlanarNikodym

/-- A compact set inside an open set admits an actual smooth compactly
supported cutoff equal to one on a neighborhood of that compact set. -/
theorem exists_compact_smooth_cutoff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K S : Set E}
    (hK : IsCompact K) (hS : IsOpen S) (hKS : K ⊆ S) :
    ∃ (χ : E → ℝ) (N : Set E), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ IsOpen N ∧ K ⊆ N ∧
      (∀ x ∈ N, χ x = 1) ∧ tsupport χ ⊆ S := by
  obtain ⟨V, hV, hKV, hVS, hVc⟩ := exists_open_between_and_isCompact_closure hK hS hKS
  obtain ⟨f, hf1, hf0, hfr⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, E)) (n := ⊤) hK.isClosed (hKV.trans (hV.subset_interior_closure))
  obtain ⟨N, hN, hKN, hN1⟩ := mem_nhdsSet_iff_exists.mp hf1
  have hfc : HasCompactSupport (f : E → ℝ) := by
    apply HasCompactSupport.intro hVc
    intro x hx
    exact hf0 x hx
  have hfs : tsupport (f : E → ℝ) ⊆ closure V := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    exact hx (hf0 x hn)
  exact ⟨f, N, f.contMDiff.contDiff, hfc, hfr, hN, hKN, hN1, hfs.trans hVS⟩

/-- Analyticity at the closed interval's endpoints supplies genuine
regularity outside the interval where a nonzero smooth cutoff must live. -/
theorem Family.exists_analytic_cutoff_neighborhood {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) (q : Parameters 2 d) (hq : q ∈ G.W) :
    ∃ (U : Set (Parameters 2 d)) (χ : ℝ × Parameters 2 d → ℝ),
      IsOpen U ∧ q ∈ U ∧ U ⊆ G.W ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ t ∈ G.I.carrier, ∀ p ∈ U, χ (t, p) = 1) ∧
      (∀ x ∈ tsupport χ, AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x) := by
  let K : Set (ℝ × Parameters 2 d) := G.I.carrier ×ˢ {q}
  let S : Set (ℝ × Parameters 2 d) :=
    {x | AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x}
  have hK : IsCompact K := isCompact_Icc.prod isCompact_singleton
  have hS : IsOpen S := isOpen_analyticAt ℝ _
  have hKS : K ⊆ S := by
    rintro ⟨t, p⟩ ⟨ht, hp⟩
    have hpq : p = q := hp
    subst p
    exact ha (t, q) ⟨ht, hq⟩
  obtain ⟨χ, N, hχ, hc, hχr, hN, hKN, hN1, hχS⟩ := exists_compact_smooth_cutoff hK hS hKS
  obtain ⟨T, U, _, hU, hIT, hqU, hTU⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hN hKN
  refine ⟨U ∩ G.W, χ, hU.inter ho, ⟨hqU (mem_singleton q), hq⟩,
    inter_subset_right, hχ, hc, hχr, ?_, hχS⟩
  intro t ht p hp
  exact hN1 (t, p) (hTU ⟨hIT ht, hp.1⟩)

/-- The same cutoff can be chosen inside the actual cinematic nondegenerate
region. This does not assert the local smoothing estimate on that region. -/
theorem Family.exists_cinematic_cutoff_neighborhood {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (hn : ∀ t ∈ G.I.carrier, ∀ p ∈ G.W, G.cinematicDet (t, p) ≠ 0)
    (q : Parameters 2 d) (hq : q ∈ G.W) :
    ∃ (U : Set (Parameters 2 d)) (χ : ℝ × Parameters 2 d → ℝ),
      IsOpen U ∧ q ∈ U ∧ U ⊆ G.W ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ t ∈ G.I.carrier, ∀ p ∈ U, χ (t, p) = 1) ∧
      (∀ x ∈ tsupport χ, AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x ∧
        G.cinematicDet x ≠ 0) := by
  let K : Set (ℝ × Parameters 2 d) := G.I.carrier ×ˢ {q}
  let S : Set (ℝ × Parameters 2 d) :=
    {x | AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x ∧
      AnalyticAt ℝ G.cinematicDet x ∧ G.cinematicDet x ≠ 0}
  have hK : IsCompact K := isCompact_Icc.prod isCompact_singleton
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    filter_upwards [hx.1.eventually_analyticAt, hx.2.1.eventually_analyticAt,
      hx.2.1.continuousAt.eventually_ne hx.2.2] with y hyγ hyd hyn
    exact ⟨hyγ, hyd, hyn⟩
  have hKS : K ⊆ S := by
    rintro ⟨t, p⟩ ⟨ht, hp⟩
    have hpq : p = q := hp
    subst p
    exact ⟨ha (t, q) ⟨ht, hq⟩, G.cinematicDet_analytic ha (t, q) ⟨ht, hq⟩,
      hn t ht q hq⟩
  obtain ⟨χ, N, hχ, hc, hχr, hN, hKN, hN1, hχS⟩ := exists_compact_smooth_cutoff hK hS hKS
  obtain ⟨T, U, _, hU, hIT, hqU, hTU⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hN hKN
  refine ⟨U ∩ G.W, χ, hU.inter ho, ⟨hqU (mem_singleton q), hq⟩,
    inter_subset_right, hχ, hc, hχr, ?_, ?_⟩
  · intro t ht p hp
    exact hN1 (t, p) (hTU ⟨hIT ht, hp.1⟩)
  · intro x hx
    exact ⟨(hχS hx).1, (hχS hx).2.2⟩

end PlanarNikodym
