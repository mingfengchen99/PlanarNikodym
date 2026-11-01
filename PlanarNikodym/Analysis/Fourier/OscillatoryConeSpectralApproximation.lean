import PlanarNikodym.Analysis.Fourier.OscillatorySymbolFourierTails
import PlanarNikodym.Analysis.Fourier.FourierSuperpositionTail

/-! Spectral approximation for actual compact oscillatory symbols,
with an arbitrary smooth frequency map. The oscillation parameter is
unrestricted. All estimates precede the frequency map and input data. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff FourierTransform
namespace PlanarNikodym

variable {P : Type*} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def oscillatoryConeAmplitude (A : E × Plane → ℂ) (H : E × Plane → ℝ)
    (α : ℝ) (q : E × Plane) : ℂ :=
  A q * unitImaginaryExponential (α * H q)

def oscillatoryConeKernel (A : E × Plane → ℂ) (H : E × Plane → ℝ)
    (α : ℝ) (ν : Plane → E) (q : E × Plane) : ℂ :=
  (Real.fourierChar (inner ℝ q.1 (ν q.2)) : ℂ) * oscillatoryConeAmplitude A H α q

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_oscillatoryConeAmplitude {A : E × Plane → ℂ} {H : E × Plane → ℝ}
    (hA : ContDiff ℝ ∞ A) (hH : ContDiff ℝ ∞ H) (α : ℝ) :
    ContDiff ℝ ∞ (oscillatoryConeAmplitude A H α) :=
  hA.mul (contDiff_unitImaginaryExponential.comp (contDiff_const.mul hH))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] in
theorem hasCompactSupport_oscillatoryConeAmplitude {A : E × Plane → ℂ}
    (hA : HasCompactSupport A) (H : E × Plane → ℝ) (α : ℝ) :
    HasCompactSupport (oscillatoryConeAmplitude A H α) :=
  hA.mul_right

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_oscillatoryConeKernel {A : E × Plane → ℂ} {H : E × Plane → ℝ}
    (hA : ContDiff ℝ ∞ A) (hH : ContDiff ℝ ∞ H) (α : ℝ)
    {ν : Plane → E} (hν : ContDiff ℝ ∞ ν) :
    ContDiff ℝ ∞ (oscillatoryConeKernel A H α ν) := by
  have hc : ContDiff ℝ ∞ (fun q : E × Plane =>
      (Real.fourierChar (inner ℝ q.1 (ν q.2)) : ℂ)) := by
    simp only [Real.fourierChar_apply]
    exact ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul (contDiff_fst.inner ℝ (hν.comp contDiff_snd)))).mul
        contDiff_const).cexp
  exact hc.mul (contDiff_oscillatoryConeAmplitude hA hH α)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasCompactSupport_oscillatoryConeKernel {A : E × Plane → ℂ}
    (hA : HasCompactSupport A) (H : E × Plane → ℝ) (α : ℝ) (ν : Plane → E) :
    HasCompactSupport (oscillatoryConeKernel A H α ν) :=
  (hasCompactSupport_oscillatoryConeAmplitude hA H α).mul_left

def oscillatoryConeExtension (A : E × Plane → ℂ) (H : E × Plane → ℝ)
    (α : ℝ) (ν : Plane → E) (g : Plane → ℂ) (x : E) : ℂ :=
  ∫ y, g y * oscillatoryConeKernel A H α ν (x, y)

def oscillatoryConeExtensionSchwartz
    (A : E × Plane → ℂ) (H : E × Plane → ℝ)
    (hA : ContDiff ℝ ∞ A) (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport A)
    (α : ℝ) (ν : Plane → E) (hν : ContDiff ℝ ∞ ν)
    (g : Plane → ℂ) (hg : Integrable g) : SchwartzMap E ℂ :=
  compactKernelIntegralSchwartz volume g hg (oscillatoryConeKernel A H α ν)
    (contDiff_oscillatoryConeKernel hA hH α hν)
    (hasCompactSupport_oscillatoryConeKernel hc H α ν)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem oscillatoryConeExtensionSchwartz_apply
    (A : E × Plane → ℂ) (H : E × Plane → ℝ)
    (hA : ContDiff ℝ ∞ A) (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport A)
    (α : ℝ) (ν : Plane → E) (hν : ContDiff ℝ ∞ ν)
    (g : Plane → ℂ) (hg : Integrable g) (x : E) :
    oscillatoryConeExtensionSchwartz A H hA hH hc α ν hν g hg x =
      oscillatoryConeExtension A H α ν g x := rfl

theorem fourier_oscillatoryConeExtensionSchwartz
    (A : E × Plane → ℂ) (H : E × Plane → ℝ)
    (hA : ContDiff ℝ ∞ A) (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport A)
    (α : ℝ) (ν : Plane → E) (hν : ContDiff ℝ ∞ ν)
    (g : Plane → ℂ) (hg : Integrable g) (ξ : E) :
    𝓕 (oscillatoryConeExtensionSchwartz A H hA hH hc α ν hν g hg) ξ =
      ∫ y, g y * 𝓕 (fun x => oscillatoryConeAmplitude A H α (x, y)) (ξ - ν y) := by
  rw [oscillatoryConeExtensionSchwartz, fourier_compactKernelIntegralSchwartz]
  congr 1
  funext y
  rw [show (fun x => oscillatoryConeKernel A H α ν (x, y)) =
    (fun x => (Real.fourierChar (inner ℝ x (ν y)) : ℂ) *
      oscillatoryConeAmplitude A H α (x, y)) from rfl]
  rw [fourier_character_modulation]

theorem exists_uniform_oscillatoryConeExtension_fourier_tail
    (A : P → E × Plane → ℂ) (H : P → E × Plane → ℝ)
    (hA : ∀ p, ContDiff ℝ ∞ (A p)) (hH : ∀ p, ContDiff ℝ ∞ (H p))
    (hc : ∀ p, HasCompactSupport (A p))
    {K : Set E} (hK : IsCompact K)
    (hs : ∀ p y, tsupport (fun x => A p (x, y)) ⊆ K)
    (hAj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p y x,
      ‖iteratedFDeriv ℝ n (fun z => A p (z, y)) x‖ ≤ B)
    (hHj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p y x,
      ‖iteratedFDeriv ℝ n (fun z => H p (z, y)) x‖ ≤ B)
    (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α (ν : Plane → E) (hν : ContDiff ℝ ∞ ν)
      (g : Plane → ℂ) (hg : Integrable g) (S : Set E),
      (∀ y, g y ≠ 0 → ν y ∈ S) →
      ∀ T : ℝ, 0 < T →
      (∫ ξ in (cthickening ((1 + |α|) * T) S)ᶜ,
        ‖𝓕 (oscillatoryConeExtensionSchwartz (A p) (H p)
          (hA p) (hH p) (hc p) α ν hν g hg) ξ‖) ≤
        (C * (1 + |α|) ^ (volume : Measure E).integrablePower * (T⁻¹) ^ M) *
          ∫ y, ‖g y‖ := by
  let A' : P × Plane → E → ℂ := fun q x => A q.1 (x, q.2)
  let H' : P × Plane → E → ℝ := fun q x => H q.1 (x, q.2)
  have hA' (q : P × Plane) : ContDiff ℝ ∞ (A' q) :=
    (hA q.1).comp (contDiff_id.prodMk contDiff_const)
  have hH' (q : P × Plane) : ContDiff ℝ ∞ (H' q) :=
    (hH q.1).comp (contDiff_id.prodMk contDiff_const)
  have hs' (q : P × Plane) : tsupport (A' q) ⊆ K := hs q.1 q.2
  have hAj' : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ q x,
      ‖iteratedFDeriv ℝ n (A' q) x‖ ≤ B := by
    intro n
    obtain ⟨B, hB, hb⟩ := hAj n
    exact ⟨B, hB, fun q => hb q.1 q.2⟩
  have hHj' : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ q x,
      ‖iteratedFDeriv ℝ n (H' q) x‖ ≤ B := by
    intro n
    obtain ⟨B, hB, hb⟩ := hHj n
    exact ⟨B, hB, fun q => hb q.1 q.2⟩
  obtain ⟨D, _, hD⟩ := exists_uniform_oscillatorySymbol_fourier_moment
    A' H' hA' hH' hK hs' hAj' hHj' 0
  obtain ⟨C, hC, ht⟩ := exists_uniform_oscillatorySymbol_fourier_tail
    A' H' hA' hH' hK hs' hAj' hHj' M
  refine ⟨C, hC, fun p α ν hν g hg S hS T hT => ?_⟩
  let B : E × Plane → ℂ := fun q =>
    𝓕 (oscillatorySymbolSchwartz A' H' hA' hH' hK hs' (p, q.2) α) q.1
  have hB : Continuous B := by
    change Continuous (fun q : E × Plane =>
      𝓕 (fun x => oscillatoryConeAmplitude (A p) (H p) α (x, q.2)) q.1)
    exact continuous_compactKernel_partialFourier
      (contDiff_oscillatoryConeAmplitude (hA p) (hH p) α)
      (hasCompactSupport_oscillatoryConeAmplitude (hc p) (H p) α)
  have hi (y : Plane) : Integrable (fun ξ => B (ξ, y)) :=
    (𝓕 (oscillatorySymbolSchwartz A' H' hA' hH' hK hs' (p, y) α)).integrable
  have hD' (y : Plane) :
      (∫ ξ, ‖B (ξ, y)‖) ≤ D * (1 + |α|) ^ (volume : Measure E).integrablePower := by
    simpa only [B, pow_zero, one_mul, zero_add] using hD (p, y) α
  have ht' (y : Plane) :
      (∫ ξ in {ξ : E | (1 + |α|) * T ≤ ‖ξ‖}, ‖B (ξ, y)‖) ≤
        C * (1 + |α|) ^ (volume : Measure E).integrablePower * (T⁻¹) ^ M :=
    ht (p, y) α T hT
  have hh := integral_fourier_superposition_tail_le volume hg hB hν.continuous
    hi hD' hS ht'
  have hBc (y : Plane) :
      (oscillatorySymbolSchwartz A' H' hA' hH' hK hs' (p, y) α : E → ℂ) =
        (fun x => oscillatoryConeAmplitude (A p) (H p) α (x, y)) := rfl
  simpa only [fourier_oscillatoryConeExtensionSchwartz, B,
    SchwartzMap.fourier_coe, hBc] using hh

/-- The approximation constant is independent of the smooth frequency
map, the oscillation parameter and the input. Oscillation enlarges the
spectral neighborhood linearly and costs only one fixed power in the
arbitrary-order error. -/
theorem exists_uniform_oscillatoryConeExtension_spectral_approximation
    (A : P → E × Plane → ℂ) (H : P → E × Plane → ℝ)
    (hA : ∀ p, ContDiff ℝ ∞ (A p)) (hH : ∀ p, ContDiff ℝ ∞ (H p))
    (hc : ∀ p, HasCompactSupport (A p))
    {K : Set E} (hK : IsCompact K)
    (hs : ∀ p y, tsupport (fun x => A p (x, y)) ⊆ K)
    (hAj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p y x,
      ‖iteratedFDeriv ℝ n (fun z => A p (z, y)) x‖ ≤ B)
    (hHj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p y x,
      ‖iteratedFDeriv ℝ n (fun z => H p (z, y)) x‖ ≤ B)
    (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α (ν : Plane → E), ContDiff ℝ ∞ ν →
      ∀ (J : Set Plane), IsCompact J →
      ∀ (g : Plane → ℂ), Integrable g → Function.support g ⊆ J →
      ∀ T : ℝ, 0 < T → ∃ F : SchwartzMap E ℂ,
        Function.support (𝓕 (F : E → ℂ)) ⊆
          cthickening (2 * ((1 + |α|) * T)) (ν '' J) ∧
        ∀ x, ‖oscillatoryConeExtension (A p) (H p) α ν g x - F x‖ ≤
          (C * (1 + |α|) ^ (volume : Measure E).integrablePower * (T⁻¹) ^ M) *
            ∫ y, ‖g y‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_oscillatoryConeExtension_fourier_tail
    A H hA hH hc hK hs hAj hHj M
  refine ⟨C, hC, fun p α ν hν J hJ g hg hgs T hT => ?_⟩
  let G := oscillatoryConeExtensionSchwartz (A p) (H p) (hA p) (hH p) (hc p)
    α ν hν g hg
  have hα : 0 < 1 + |α| := by positivity
  obtain ⟨F, hsF, he⟩ := exists_schwartz_neighborhood_approximation G
    (hJ.image hν.continuous) (mul_pos hα hT)
  refine ⟨F, hsF, fun x => (he x).trans ?_⟩
  exact hb p α ν hν g hg (ν '' J) (fun y hy => ⟨y, hgs hy, rfl⟩) T hT

end PlanarNikodym
