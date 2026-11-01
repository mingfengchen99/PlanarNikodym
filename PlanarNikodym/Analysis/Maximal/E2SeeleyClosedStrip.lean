import PlanarNikodym.Analysis.Maximal.E2SeeleyTranslatedHalfSpace
import PlanarNikodym.Analysis.Localization.AnalyticCutoff

/-! A jointly C∞ extension of an actual compactly supported function on
a nondegenerate closed time strip. The two endpoint extensions are
constructed and summed using a finite smooth splitting. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem e2_exists_contDiff_extension_closed_strip {a b : ℝ} (hab : a < b)
    {f : (ℝ × E) → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ))
    (hc : HasCompactSupport f) :
    ∃ g : (ℝ × E) → ℝ, ContDiff ℝ ∞ g ∧ EqOn g f (Icc a b ×ˢ univ) := by
  classical
  obtain ⟨χ, N, hχ, _, _, hN, haN, hχ1, hsχ⟩ :=
    exists_compact_smooth_cutoff (K := {a}) isCompact_singleton isOpen_Iio
      (show ({a} : Set ℝ) ⊆ Iio b by simpa using hab)
  let fL : (ℝ × E) → ℝ := fun x => χ x.1 * f x
  let fR : (ℝ × E) → ℝ := (Ici a ×ˢ univ).indicator (f - fL)
  have hLc : HasCompactSupport fL := hc.mul_left
  have hRc : HasCompactSupport fR := by
    apply HasCompactSupport.intro (hc.sub hLc).isCompact
    intro x hx
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hx).self_of_nhds
    simp only [fR, indicator]
    split_ifs
    · exact hz
    · rfl
  have hLs : ContDiffOn ℝ ∞ fL (Ici a ×ˢ univ) := by
    intro x hx
    by_cases hxs : x.1 ∈ tsupport χ
    · have hxb : x.1 < b := hsχ hxs
      have hfn : ContDiffWithinAt ℝ ∞ f (Ici a ×ˢ univ) x :=
        (hf x ⟨⟨hx.1, hxb.le⟩, mem_univ _⟩).mono_of_mem_nhdsWithin (by
          have hn := continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds hxb)
          filter_upwards [self_mem_nhdsWithin, (Filter.Eventually.filter_mono inf_le_left (show ∀ᶠ y in 𝓝 x, y.1 < b from hn))] with y hy hyn
          exact ⟨⟨hy.1, (show y.1 < b from hyn).le⟩, mem_univ _⟩)
      exact (hχ.comp contDiff_fst).contDiffWithinAt.mul hfn
    · have he : fL =ᶠ[𝓝 x] 0 := by
        have hn := continuous_fst.continuousAt.tendsto.eventually
          (notMem_tsupport_iff_eventuallyEq.mp hxs)
        filter_upwards [hn] with y hy
        simp only [fL, Pi.zero_apply] at hy ⊢
        rw [hy, zero_mul]
      exact contDiffWithinAt_const.congr_of_eventuallyEq
        (he.filter_mono inf_le_left) he.self_of_nhds
  have hRs : ContDiffOn ℝ ∞ fR (Iic b ×ˢ univ) := by
    intro x hx
    rcases lt_trichotomy x.1 a with hxa | hxa | hxa
    · have he : fR =ᶠ[𝓝 x] 0 := by
        have hn := continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds hxa)
        filter_upwards [hn] with y hy
        simp only [fR, indicator_of_notMem (show y ∉ Ici a ×ˢ univ from
          fun hh => not_le_of_gt (show y.1 < a from hy) hh.1), Pi.zero_apply]
      exact contDiffWithinAt_const.congr_of_eventuallyEq
        (he.filter_mono inf_le_left) he.self_of_nhds
    · have he : fR =ᶠ[𝓝 x] 0 := by
        have hxN : x.1 ∈ N := hxa ▸ haN (mem_singleton a)
        have hn := continuous_fst.continuousAt.preimage_mem_nhds (hN.mem_nhds hxN)
        filter_upwards [hn] with y hy
        have hy1 := hχ1 y.1 hy
        simp [fR, fL, hy1]
      exact contDiffWithinAt_const.congr_of_eventuallyEq
        (he.filter_mono inf_le_left) he.self_of_nhds
    · have hfn : ContDiffWithinAt ℝ ∞ f (Iic b ×ˢ univ) x :=
        (hf x ⟨⟨hxa.le, hx.1⟩, mem_univ _⟩).mono_of_mem_nhdsWithin (by
          have hn := continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hxa)
          filter_upwards [self_mem_nhdsWithin, (Filter.Eventually.filter_mono inf_le_left (show ∀ᶠ y in 𝓝 x, a < y.1 from hn))] with y hy hyn
          exact ⟨⟨(show a < y.1 from hyn).le, hy.1⟩, mem_univ _⟩)
      have hd : ContDiffWithinAt ℝ ∞ (f - fL) (Iic b ×ˢ univ) x :=
        hfn.sub ((hχ.comp contDiff_fst).contDiffWithinAt.mul hfn)
      have he : fR =ᶠ[𝓝 x] (f - fL) := by
        have hn := continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hxa)
        filter_upwards [hn] with y hy
        exact indicator_of_mem (show y ∈ Ici a ×ˢ univ from ⟨(show a < y.1 from hy).le, mem_univ _⟩) _
      exact hd.congr_of_eventuallyEq (he.filter_mono inf_le_left) he.self_of_nhds
  obtain ⟨gL, hgL, heL⟩ := e2_exists_extension_left_halfspace a hLs hLc
  obtain ⟨gR, hgR, heR⟩ := e2_exists_extension_right_halfspace b hRs hRc
  refine ⟨gL + gR, hgL.add hgR, ?_⟩
  intro x hx
  have hxl : x ∈ Ici a ×ˢ univ := ⟨hx.1.1, mem_univ _⟩
  have hxr : x ∈ Iic b ×ˢ univ := ⟨hx.1.2, mem_univ _⟩
  simp only [Pi.add_apply, heL hxl, heR hxr, fR, indicator_of_mem hxl, Pi.sub_apply]
  ring

end PlanarNikodym
