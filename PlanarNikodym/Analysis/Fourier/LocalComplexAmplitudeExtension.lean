import PlanarNikodym.Analysis.Localization.SmoothCompactExtension

/-! A genuine compact smooth complex extension of a locally smooth
amplitude. The extension also preserves all zero values, so existing
input windows continue to cut off the actual integrand. -/
noncomputable section
open Set Filter
open scoped ContDiff
namespace PlanarNikodym

theorem exists_compact_smooth_complex_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : E → ℂ) {K S : Set E} (hK : IsCompact K) (hS : IsOpen S) (hKS : K ⊆ S)
    (hH : ∀ x ∈ S, ContDiffAt ℝ ∞ H x) :
    ∃ (B : E → ℂ) (N : Set E), ContDiff ℝ ∞ B ∧ HasCompactSupport B ∧
      IsOpen N ∧ K ⊆ N ∧ N ⊆ S ∧ EqOn B H N ∧
      ∀ x, H x = 0 → B x = 0 := by
  obtain ⟨χ, N, hχ, hc, _, hN, hKN, hN1, hχS⟩ :=
    exists_compact_smooth_cutoff hK hS hKS
  let B : E → ℂ := fun x => (χ x : ℂ) * H x
  have hB : ContDiff ℝ ∞ B := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact (Complex.ofRealCLM.contDiff.comp hχ).contDiffAt.mul (hH x (hχS hx))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [B, Pi.zero_apply] at hy ⊢
      rw [hy, Complex.ofReal_zero, zero_mul]
  refine ⟨B, N ∩ S, hB, (hc.comp_left (g := Complex.ofRealCLM) rfl).mul_right,
    hN.inter hS, fun x hx => ⟨hKN hx, hKS hx⟩, inter_subset_right, ?_, ?_⟩
  · intro x hx
    simp only [B, hN1 x hx.1, Complex.ofReal_one, one_mul]
  · intro x hx
    simp only [B, hx, mul_zero]

end PlanarNikodym
