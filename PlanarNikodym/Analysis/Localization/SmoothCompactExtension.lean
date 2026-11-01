import PlanarNikodym.Analysis.Localization.AnalyticCutoff
import PlanarNikodym.Analysis.Fourier.TimeTaylorApproximation

/-! Compactly local smooth phases have genuine global smooth extensions.
The extension agrees on an open neighborhood, so it preserves all actual
derivatives used in the time Taylor polynomial. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace PlanarNikodym

theorem exists_compact_smooth_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Φ : E → ℝ) {K S : Set E} (hK : IsCompact K) (hS : IsOpen S) (hKS : K ⊆ S)
    (hΦ : ∀ x ∈ S, ContDiffAt ℝ ∞ Φ x) :
    ∃ (Ψ : E → ℝ) (N : Set E), ContDiff ℝ ∞ Ψ ∧ HasCompactSupport Ψ ∧
      IsOpen N ∧ K ⊆ N ∧ N ⊆ S ∧ EqOn Ψ Φ N := by
  obtain ⟨χ, N, hχ, hc, _, hN, hKN, hN1, hχS⟩ :=
    exists_compact_smooth_cutoff hK hS hKS
  let Ψ : E → ℝ := fun x => χ x * Φ x
  have hΨ : ContDiff ℝ ∞ Ψ := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact hχ.contDiffAt.mul (hΦ x (hχS hx))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [Ψ, Pi.zero_apply] at hy ⊢
      rw [hy, zero_mul]
  refine ⟨Ψ, N ∩ S, hΨ, hc.mul_right, hN.inter hS,
    fun x hx => ⟨hKN hx, hKS hx⟩, inter_subset_right, ?_⟩
  intro x hx
  simp only [Ψ, hN1 x hx.1, one_mul]

/-- Agreement on an open parameter-time neighborhood preserves the
Taylor polynomial as a function of its endpoint, in every degree. -/
theorem timeTaylorEval_eq_of_eqOn_open
    {P : Type} [TopologicalSpace P] (Φ Ψ : P × ℝ → ℝ)
    {S : Set (P × ℝ)} (hS : IsOpen S) (heq : EqOn Φ Ψ S)
    (n : ℕ) (p : P) (c t : ℝ) (hc : (p, c) ∈ S) :
    timeTaylorEval Φ n p c t = timeTaylorEval Ψ n p c t := by
  have he : (fun s : ℝ => Φ (p, s)) =ᶠ[𝓝 c] fun s => Ψ (p, s) := by
    have hpre := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hS.mem_nhds hc)
    filter_upwards [hpre] with s hs
    exact heq hs
  unfold timeTaylorEval
  apply Finset.sum_congr rfl
  intro i _
  rw [he.iteratedDeriv_eq i]

end PlanarNikodym
