import PlanarNikodym.Analysis.Maximal.E2SeeleyClosedStrip
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-! Actual joint C∞ extension from a closed time interval and an open
parameter set, on an arbitrary compact parameter subset. It preserves
all canonical within Taylor jets, including the closed time endpoints. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem e2_exists_contDiff_extension_closed_product {a b : ℝ} (hab : a < b)
    {W K : Set E} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    {f : (ℝ × E) → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ W)) :
    ∃ (g : (ℝ × E) → ℝ) (N : Set (ℝ × E)), ContDiff ℝ ∞ g ∧
      IsOpen N ∧ Icc a b ×ˢ K ⊆ N ∧ EqOn g f ((Icc a b ×ˢ univ) ∩ N) := by
  obtain ⟨χ, N, hχ, hcχ, _, hN, hKN, hχ1, hsχ⟩ :=
    exists_compact_smooth_cutoff (isCompact_Icc.prod hK) (isOpen_univ.prod hW)
      (show Icc a b ×ˢ K ⊆ univ ×ˢ W from fun _ hx => ⟨mem_univ _, hKW hx.2⟩)
  let f₀ : (ℝ × E) → ℝ := fun x => χ x * f x
  have hfc : HasCompactSupport f₀ := hcχ.mul_right
  have hfs : ContDiffOn ℝ ∞ f₀ (Icc a b ×ˢ univ) := by
    intro x hx
    by_cases hxs : x ∈ tsupport χ
    · have hxW : x.2 ∈ W := (hsχ hxs).2
      have hfn : ContDiffWithinAt ℝ ∞ f (Icc a b ×ˢ univ) x :=
        (hf x ⟨hx.1, hxW⟩).mono_of_mem_nhdsWithin (by
          have hn : ∀ᶠ y in 𝓝 x, y.2 ∈ W :=
            continuous_snd.continuousAt.preimage_mem_nhds (hW.mem_nhds hxW)
          filter_upwards [self_mem_nhdsWithin, hn.filter_mono inf_le_left] with y hy hyW
          exact ⟨hy.1, hyW⟩)
      exact hχ.contDiffWithinAt.mul hfn
    · have he : f₀ =ᶠ[𝓝 x] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxs] with y hy
        simp only [f₀, Pi.zero_apply] at hy ⊢
        rw [hy, zero_mul]
      exact contDiffWithinAt_const.congr_of_eventuallyEq
        (he.filter_mono inf_le_left) he.self_of_nhds
  obtain ⟨g, hg, he⟩ := e2_exists_contDiff_extension_closed_strip hab hfs hfc
  refine ⟨g, N, hg, hN, hKN, ?_⟩
  intro x hx
  rw [he hx.1]
  simp only [f₀, hχ1 x hx.2, one_mul]

theorem e2_exists_contDiff_extension_closed_product_with_jets {a b : ℝ} (hab : a < b)
    {W K : Set E} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    {f : (ℝ × E) → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ W)) :
    ∃ (g : (ℝ × E) → ℝ), ContDiff ℝ ∞ g ∧ EqOn g f (Icc a b ×ˢ K) ∧
      ∀ x ∈ Icc a b ×ˢ K, ∀ m : ℕ,
        iteratedFDeriv ℝ m g x = iteratedFDerivWithin ℝ m f (Icc a b ×ˢ W) x := by
  obtain ⟨g, N, hg, hN, hKN, he⟩ :=
    e2_exists_contDiff_extension_closed_product hab hW hK hKW hf
  have hS : UniqueDiffOn ℝ (Icc a b ×ˢ W) := (uniqueDiffOn_Icc hab).prod hW.uniqueDiffOn
  have heK : EqOn g f (Icc a b ×ˢ K) := fun x hx => he ⟨⟨hx.1, mem_univ _⟩, hKN hx⟩
  refine ⟨g, hg, heK, ?_⟩
  intro x hx m
  have hxS : x ∈ Icc a b ×ˢ W := ⟨hx.1, hKW hx.2⟩
  have hn : g =ᶠ[𝓝[Icc a b ×ˢ W] x] f := by
    filter_upwards [self_mem_nhdsWithin, (Filter.Eventually.filter_mono inf_le_left
      (show ∀ᶠ y in 𝓝 x, y ∈ N from hN.mem_nhds (hKN hx)))] with y hy hyN
    exact he ⟨⟨hy.1, mem_univ _⟩, hyN⟩
  have hj := hn.iteratedFDerivWithin_eq (𝕜 := ℝ) (heK hx) m
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hS (hg.of_le (by
    exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top))).contDiffAt hxS] at hj
  exact hj

end PlanarNikodym
