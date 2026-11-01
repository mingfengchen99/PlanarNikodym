import PlanarNikodym.Analysis.Localization.ScaleTimeLocalization
import PlanarNikodym.Analysis.Localization.AnalyticCutoff

/-! A compact cutoff support inside an open regular region has one
compact time enlargement and one positive scale threshold. All centers
and full time segments of the scale pieces stay inside that enlargement. -/

noncomputable section
open Set Metric
open scoped Topology ContDiff

namespace PlanarNikodym

theorem exists_compact_regular_time_neighborhood
    {P : Type*} [TopologicalSpace P] {K S : Set (ℝ × P)}
    (hK : IsCompact K) (hS : IsOpen S) (hKS : K ⊆ S) :
    ∃ (ε : ℝ) (L : Set (ℝ × P)), 0 < ε ∧ IsCompact L ∧ K ⊆ L ∧ L ⊆ S ∧
      ∀ x ∈ K, ∀ h : ℝ, |h| ≤ ε → (x.1 + h, x.2) ∈ L := by
  let F : ℝ × (ℝ × P) → ℝ × P := fun q => (q.2.1 + q.1, q.2.2)
  have hF : Continuous F := (continuous_snd.fst.add continuous_fst).prodMk continuous_snd.snd
  have hpre : ({0} : Set ℝ) ×ˢ K ⊆ F ⁻¹' S := by
    rintro ⟨h, x⟩ ⟨hh, hx⟩
    have hz : h = 0 := hh
    simpa only [F, hz, add_zero, mem_preimage] using hKS hx
  obtain ⟨T, V, hT, _, h0T, hKV, hTV⟩ :=
    generalized_tube_lemma isCompact_singleton hK (hS.preimage hF) hpre
  have hz : (0 : ℝ) ∈ T := h0T (by simp)
  obtain ⟨r, hr, hrT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds hz)
  let ε : ℝ := r / 2
  let L : Set (ℝ × P) := F '' (Icc (-ε) ε ×ˢ K)
  have hε : 0 < ε := half_pos hr
  refine ⟨ε, L, hε, (isCompact_Icc.prod hK).image hF, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨(0, x), ⟨⟨by linarith, hε.le⟩, hx⟩, by simp [F]⟩
  · rintro _ ⟨⟨h, x⟩, ⟨hh, hx⟩, rfl⟩
    have habs : |h| ≤ ε := abs_le.mpr hh
    have hhball : h ∈ ball (0 : ℝ) r := by
      rw [mem_ball, Real.dist_eq, sub_zero]
      exact habs.trans_lt (by dsimp [ε]; linarith)
    exact hTV ⟨hrT hhball, hKV hx⟩
  · intro x hx h hh
    exact ⟨(h, x), ⟨abs_le.mp hh, hx⟩, rfl⟩

/-- The threshold is constructed from the original support. For every
time piece that meets it, its whole closed time interval at that same
parameter lies in one compact regular set, independently of the piece. -/
theorem exists_regular_scaleTimeLocalized_neighborhood
    {P : Type} [TopologicalSpace P] (χ : ℝ × P → ℝ) (hc : HasCompactSupport χ)
    {S : Set (ℝ × P)} (hS : IsOpen S) (hs : tsupport χ ⊆ S) :
    ∃ (ε : ℝ) (L : Set (ℝ × P)), 0 < ε ∧ IsCompact L ∧ tsupport χ ⊆ L ∧ L ⊆ S ∧
      ∀ (a δ : ℝ), 0 < δ → δ ≤ ε / 2 → ∀ (i : ℕ) (x : ℝ × P),
        x ∈ tsupport (scaleTimeLocalizedCutoff χ a δ i) →
        ∀ s : ℝ, |s - (a + (i : ℝ) * δ)| ≤ δ → (s, x.2) ∈ L := by
  obtain ⟨ε, L, hε, hL, hχL, hLS, hshift⟩ :=
    exists_compact_regular_time_neighborhood hc.isCompact hS hs
  refine ⟨ε, L, hε, hL, hχL, hLS, ?_⟩
  intro a δ hδ hδε i x hx s hs'
  have hxχ := tsupport_scaleTimeLocalizedCutoff_subset χ a δ i hx
  have hxt := scaleTimeLocalizedCutoff_time_support χ a hδ i hx
  have hcenter : |x.1 - (a + (i : ℝ) * δ)| ≤ δ :=
    abs_le.mpr ⟨by nlinarith [hxt.1], by nlinarith [hxt.2]⟩
  have hdist : |s - x.1| ≤ ε := by
    calc
      _ ≤ |s - (a + (i : ℝ) * δ)| + |(a + (i : ℝ) * δ) - x.1| := abs_sub_le _ _ _
      _ ≤ δ + δ := add_le_add hs' (by simpa only [abs_sub_comm] using hcenter)
      _ ≤ ε := by linarith
  simpa only [add_sub_cancel] using hshift x hxχ (s - x.1) hdist

/-- In particular, the center and the full segment to each normalized
time lie in the regular compact set. The witnesses come from the original
cutoff support and are shared by every sufficiently small time piece. -/
theorem exists_regular_scaleTimeLocalized_segments
    {P : Type} [TopologicalSpace P] (χ : ℝ × P → ℝ) (hc : HasCompactSupport χ)
    {S : Set (ℝ × P)} (hS : IsOpen S) (hs : tsupport χ ⊆ S) :
    ∃ (ε : ℝ) (L : Set (ℝ × P)), 0 < ε ∧ IsCompact L ∧ tsupport χ ⊆ L ∧ L ⊆ S ∧
      ∀ (a δ : ℝ), 0 < δ → δ ≤ ε / 2 → ∀ (i : ℕ) (x : ℝ × P),
        x ∈ tsupport (scaleTimeLocalizedCutoff χ a δ i) →
        ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ s ∈ uIcc (a + (i : ℝ) * δ) (a + (i : ℝ) * δ + δ * τ),
          (s, x.2) ∈ L := by
  obtain ⟨ε, L, hε, hL, hχL, hLS, hspan⟩ :=
    exists_regular_scaleTimeLocalized_neighborhood χ hc hS hs
  refine ⟨ε, L, hε, hL, hχL, hLS, ?_⟩
  intro a δ hδ hδε i x hx τ hτ s hs'
  apply hspan a δ hδ hδε i x hx s
  have hτabs : |τ| ≤ 1 := abs_le.mpr hτ
  calc
    _ ≤ |(a + (i : ℝ) * δ + δ * τ) - (a + (i : ℝ) * δ)| := abs_sub_left_of_mem_uIcc hs'
    _ = δ * |τ| := by rw [add_sub_cancel_left, abs_mul, abs_of_pos hδ]
    _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hτabs hδ.le
    _ = δ := mul_one δ

end PlanarNikodym
