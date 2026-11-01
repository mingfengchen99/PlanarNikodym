import PlanarNikodym.Analysis.Fourier.TimeSliceExtension
import PlanarNikodym.Analysis.Fourier.InverseChartAmplitude

/-! The uniform amplitude theorem applies to phases which are smooth
only near the actual regular compact set. A smooth extension is
constructed, and its amplitude agrees exactly with the original one
whenever the actual center and endpoint belong to that compact set. -/
noncomputable section
open Set
open scoped ContDiff
namespace PlanarNikodym

theorem rescaledTaylorAmplitude_eq_actualTaylorAmplitude
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (a : P × ℝ × ℝ → ℂ) {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (n : ℕ) (p : P) (r c δ τ η : ℝ) :
    rescaledTaylorAmplitude a Φ n (((p, c, τ), η), r * δ ^ (n + 1), δ) =
      actualTaylorAmplitude a Φ n r c δ p τ η := by
  unfold rescaledTaylorAmplitude actualTaylorAmplitude frequencyTaylorCorrection
  rw [taylorPhaseCorrection_eq hΦ]

theorem exists_local_smooth_Taylor_amplitude
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (Φ : P × ℝ → ℝ) {L S : Set (P × ℝ)} (hL : IsCompact L)
    (hS : IsOpen S) (hLS : L ⊆ S) (hΦ : ∀ x ∈ S, ContDiffAt ℝ ∞ Φ x) :
    ∃ Ψ : P × ℝ → ℝ, ContDiff ℝ ∞ Ψ ∧ HasCompactSupport Ψ ∧
      ∀ (a : P × ℝ × ℝ → ℂ) (n : ℕ) (p : P) (r c δ τ η : ℝ),
        (p, c) ∈ L → (p, c + δ * τ) ∈ L →
        actualTaylorAmplitude a Φ n r c δ p τ η =
          rescaledTaylorAmplitude a Ψ n (((p, c, τ), η), r * δ ^ (n + 1), δ) := by
  obtain ⟨Ψ, N, hΨ, hcΨ, hN, hLN, _, heq⟩ := exists_compact_smooth_extension Φ hL hS hLS hΦ
  refine ⟨Ψ, hΨ, hcΨ, ?_⟩
  intro a n p r c δ τ η hc ht
  rw [rescaledTaylorAmplitude_eq_actualTaylorAmplitude a hΨ]
  unfold actualTaylorAmplitude frequencyTaylorCorrection
  rw [heq (hLN ht), timeTaylorEval_eq_of_eqOn_open Ψ Φ hN heq n p c _ (hLN hc)]

end PlanarNikodym
