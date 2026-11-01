import PlanarNikodym.Analysis.Fourier.GlyzRawKernel
import PlanarNikodym.Analysis.Localization.SmoothCompactExtension

/-! Local smooth phases may be replaced by actual global smooth phases.
The replacement preserves every cinematic derivative near the amplitude
support and preserves the original extension, with the same amplitude. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace PlanarNikodym

theorem eventuallyEq_timeDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ × E → ℝ} {x : ℝ × E} (h : f =ᶠ[𝓝 x] g) (j : ℕ) :
    timeDerivative f j =ᶠ[𝓝 x] timeDerivative g j := by
  induction j with
  | zero => exact h
  | succ j ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L : (ℝ × E) →L[ℝ] ℝ => L (1, 0)) hy

theorem Family.cinematicDet_eq_of_eventuallyEq {d : ℕ}
    (G H : Family 2 d) {x : ℝ × Parameters 2 d}
    (h : (fun z : ℝ × Parameters 2 d => G.γ z.1 z.2) =ᶠ[𝓝 x]
      fun z => H.γ z.1 z.2) : G.cinematicDet x = H.cinematicDet x := by
  apply congrArg Matrix.det
  funext i j
  apply (eventuallyEq_timeDerivative (j := (i : ℕ)) ?_).eq_of_nhds
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L : (ℝ × Parameters 2 d) →L[ℝ] ℝ =>
    L (0, parameterFrame d (Pi.single j 1))) hy

theorem glyzRawExtension_eq_of_phase_eq_on_amplitude {P : Type}
    (Φ Ψ : P × ℝ → ℝ) (a : P × Plane → ℂ)
    (heq : ∀ p t η, a (p, t, η) ≠ 0 → Φ (p, t) = Ψ (p, t))
    (g : Plane → ℂ) (r : ℝ) :
    glyzRawExtension Φ a g r = glyzRawExtension Ψ a g r := by
  funext p
  unfold glyzRawExtension
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ha : a (p, t, η) = 0
  · simp only [ha, mul_zero, zero_mul]
  · simp only [phaseOscillation, heq p t η ha]

/-- The actual family and all original extensions agree after smooth
extension from a neighborhood of a fixed compact time-parameter set. -/
theorem Family.exists_glyz_global_smooth_phase {d : ℕ} (G : Family 2 d)
    {K U : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hG : ∀ x ∈ U, ContDiffAt ℝ ∞
      (fun z : ℝ × Parameters 2 d => G.γ z.1 z.2) x) :
    ∃ H : Family 2 d,
      H.I = G.I ∧ H.W = G.W ∧
      ContDiff ℝ ∞ (fun z : ℝ × Parameters 2 d => H.γ z.1 z.2) ∧
      (∀ x ∈ K, H.cinematicDet x = G.cinematicDet x) ∧
      ∀ a : Parameters 2 d × Plane → ℂ,
        (∀ p t η, a (p, t, η) ≠ 0 → (t, p) ∈ K) →
        ∀ g : Plane → ℂ, ∀ r : ℝ,
          glyzRawExtension (fun z => H.γ z.2 z.1) a g r =
            glyzRawExtension (fun z => G.γ z.2 z.1) a g r := by
  obtain ⟨Ψ, V, hΨ, _, hV, hKV, _, heq⟩ :=
    exists_compact_smooth_extension
      (fun z : ℝ × Parameters 2 d => G.γ z.1 z.2) hK hU hKU hG
  let H : Family 2 d := { G with γ := fun t p => Ψ (t, p) }
  refine ⟨H, rfl, rfl, hΨ, ?_, ?_⟩
  · intro x hx
    apply H.cinematicDet_eq_of_eventuallyEq G
    filter_upwards [hV.mem_nhds (hKV hx)] with y hy
    exact heq hy
  · intro a ha g r
    apply glyzRawExtension_eq_of_phase_eq_on_amplitude
    intro p t η hn
    exact heq (hKV (ha p t η hn))

end PlanarNikodym
