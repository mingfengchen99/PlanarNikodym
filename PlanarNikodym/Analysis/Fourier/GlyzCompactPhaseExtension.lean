import PlanarNikodym.Analysis.Fourier.LocalComplexAmplitudeExtension

/-! Compact extension of a phase and amplitude that preserves the exact
oscillatory integrand up to an explicit cutoff in the original chart. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace PlanarNikodym

theorem exists_glyz_compact_phase_amplitude
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (a : E → ℂ) (h : E → ℝ) {K S : Set E}
    (hK : IsCompact K) (hS : IsOpen S) (hKS : K ⊆ S)
    (ha : ∀ x ∈ S, ContDiffAt ℝ ∞ a x) (hh : ∀ x ∈ S, ContDiffAt ℝ ∞ h x) :
    ∃ (ρ : E → ℝ) (A : E → ℂ) (H : E → ℝ),
      ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x ∧ ρ x ≤ 1) ∧
      (∀ x ∈ K, ρ x = 1) ∧ tsupport ρ ⊆ S ∧
      ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧ tsupport A ⊆ S ∧
      ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ S ∧
      (∀ x, A x = (ρ x : ℂ) * a x) ∧
      ∀ x α, A x * Complex.exp (((α * H x : ℝ) : ℂ) * Complex.I) =
        (ρ x : ℂ) * (a x * Complex.exp (((α * h x : ℝ) : ℂ) * Complex.I)) := by
  obtain ⟨ρ, N, hρ, hcρ, hρrange, _, hKN, hN1, hρS⟩ :=
    exists_compact_smooth_cutoff hK hS hKS
  obtain ⟨ψ, M, hψ, hcψ, _, _, hρM, hM1, hψS⟩ :=
    exists_compact_smooth_cutoff hcρ.isCompact hS hρS
  let A : E → ℂ := fun x => (ρ x : ℂ) * a x
  let H : E → ℝ := fun x => ψ x * h x
  have hA : ContDiff ℝ ∞ A := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport ρ
    · exact (Complex.ofRealCLM.contDiff.comp hρ).contDiffAt.mul (ha x (hρS hx))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [A, hy, Complex.ofReal_zero, zero_mul]
  have hH : ContDiff ℝ ∞ H := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport ψ
    · exact hψ.contDiffAt.mul (hh x (hψS hx))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [H, hy, zero_mul]
  have hAS : tsupport A ⊆ S := by
    apply subset_trans tsupport_mul_subset_left
    exact (tsupport_comp_subset (g := (Complex.ofReal : ℝ → ℂ)) (by simp) ρ).trans hρS
  refine ⟨ρ, A, H, hρ, hcρ, hρrange, fun x hx => hN1 x (hKN hx), hρS,
    hA, (hcρ.comp_left (g := Complex.ofRealCLM) rfl).mul_right, hAS,
    hH, hcψ.mul_right, tsupport_mul_subset_left.trans hψS, fun _ => rfl, ?_⟩
  intro x α
  by_cases hx : ρ x = 0
  · simp only [A, hx, Complex.ofReal_zero, zero_mul]
  · have hHx : H x = h x := by
      change ψ x * h x = h x
      rw [hM1 x (hρM (subset_tsupport _ hx)), one_mul]
    rw [hHx]
    exact mul_assoc _ _ _

/-- A prescribed smooth compact cutoff is retained exactly, rather than
replaced by a cutoff depending on additional variables. -/
theorem exists_glyz_compact_phase_amplitude_of_cutoff
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (a : E → ℂ) (h : E → ℝ) (χ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {S : Set E} (hS : IsOpen S) (hχS : tsupport χ ⊆ S)
    (ha : ∀ x ∈ S, ContDiffAt ℝ ∞ a x) (hh : ∀ x ∈ S, ContDiffAt ℝ ∞ h x) :
    ∃ (A : E → ℂ) (H : E → ℝ),
      ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧ tsupport A ⊆ S ∧
      ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ S ∧
      (∀ x, A x = (χ x : ℂ) * a x) ∧
      ∀ x α, A x * Complex.exp (((α * H x : ℝ) : ℂ) * Complex.I) =
        (χ x : ℂ) * (a x * Complex.exp (((α * h x : ℝ) : ℂ) * Complex.I)) := by
  obtain ⟨ρ, A, H, _, _, _, hρ1, _, hA, hcA, _, hH, hcH, hHS, hAe, heq⟩ :=
    exists_glyz_compact_phase_amplitude a h hcχ.isCompact hS hχS ha hh
  let B : E → ℂ := fun x => (χ x : ℂ) * A x
  have hBS : tsupport B ⊆ S :=
    tsupport_mul_subset_left.trans
      ((tsupport_comp_subset (g := (Complex.ofReal : ℝ → ℂ)) (by simp) χ).trans hχS)
  refine ⟨B, H, (Complex.ofRealCLM.contDiff.comp hχ).mul hA,
    hcA.mul_left, hBS, hH, hcH, hHS, ?_, ?_⟩
  · intro x
    by_cases hx : χ x = 0
    · simp only [B, hx, Complex.ofReal_zero, zero_mul]
    · simp only [B, hAe, hρ1 x (subset_tsupport _ hx), Complex.ofReal_one, one_mul]
  · intro x α
    change ((χ x : ℂ) * A x) * _ = _
    rw [mul_assoc, heq]
    by_cases hx : χ x = 0
    · simp only [hx, Complex.ofReal_zero, zero_mul]
    · rw [hρ1 x (subset_tsupport _ hx), Complex.ofReal_one, one_mul]

end PlanarNikodym
