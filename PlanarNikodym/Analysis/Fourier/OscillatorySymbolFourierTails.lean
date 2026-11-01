import PlanarNikodym.Analysis.Fourier.OscillatorySymbolJets
import PlanarNikodym.Analysis.Fourier.PolynomialOscillationFourierTails

/-! The actual compact symbol `A exp(i α H)`, its Schwartz realization,
and quantitative Fourier tails for every real oscillation parameter. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform
namespace PlanarNikodym

variable {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def oscillatorySymbolSchwartz
    (A : P → E → ℂ) (H : P → E → ℝ)
    (hA : ∀ p, ContDiff ℝ ∞ (A p)) (hH : ∀ p, ContDiff ℝ ∞ (H p))
    {K : Set E} (hK : IsCompact K) (hs : ∀ p, tsupport (A p) ⊆ K)
    (p : P) (α : ℝ) : SchwartzMap E ℂ :=
  HasCompactSupport.toSchwartzMap
    (hK.of_isClosed_subset (isClosed_tsupport _)
      ((show tsupport (oscillatorySymbol A H p α) ⊆ tsupport (A p) from
        tsupport_mul_subset_left).trans (hs p)))
    ((hA p).mul (contDiff_unitImaginaryExponential.comp (contDiff_const.mul (hH p))))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem oscillatorySymbolSchwartz_apply
    (A : P → E → ℂ) (H : P → E → ℝ)
    (hA : ∀ p, ContDiff ℝ ∞ (A p)) (hH : ∀ p, ContDiff ℝ ∞ (H p))
    {K : Set E} (hK : IsCompact K) (hs : ∀ p, tsupport (A p) ⊆ K)
    (p : P) (α : ℝ) (x : E) :
    oscillatorySymbolSchwartz A H hA hH hK hs p α x =
      A p x * Complex.exp (((α * H p x : ℝ) : ℂ) * Complex.I) := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem tsupport_oscillatorySymbolSchwartz_subset
    (A : P → E → ℂ) (H : P → E → ℝ)
    (hA : ∀ p, ContDiff ℝ ∞ (A p)) (hH : ∀ p, ContDiff ℝ ∞ (H p))
    {K : Set E} (hK : IsCompact K) (hs : ∀ p, tsupport (A p) ⊆ K)
    (p : P) (α : ℝ) :
    tsupport (oscillatorySymbolSchwartz A H hA hH hK hs p α) ⊆ K :=
  (show tsupport (oscillatorySymbol A H p α) ⊆ tsupport (A p) from
    tsupport_mul_subset_left).trans (hs p)

theorem exists_uniform_oscillatorySymbol_fourier_tail
    (A : P → E → ℂ) (H : P → E → ℝ)
    (hA : ∀ p, ContDiff ℝ ∞ (A p)) (hH : ∀ p, ContDiff ℝ ∞ (H p))
    {K : Set E} (hK : IsCompact K) (hs : ∀ p, tsupport (A p) ⊆ K)
    (hAj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p x, ‖iteratedFDeriv ℝ n (A p) x‖ ≤ B)
    (hHj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p x, ‖iteratedFDeriv ℝ n (H p) x‖ ≤ B)
    (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α T, 0 < T →
      (∫ ξ in {ξ : E | (1 + |α|) * T ≤ ‖ξ‖},
        ‖𝓕 (oscillatorySymbolSchwartz A H hA hH hK hs p α) ξ‖) ≤
          C * (1 + |α|) ^ (volume : Measure E).integrablePower * (T⁻¹) ^ M :=
  exists_uniform_polynomial_fourier_tail
    (oscillatorySymbolSchwartz A H hA hH hK hs) hK
    (tsupport_oscillatorySymbolSchwartz_subset A H hA hH hK hs)
    (exists_uniform_oscillatorySymbol_jet_bound A H hA hH hAj hHj) M

theorem exists_uniform_oscillatorySymbol_fourier_moment
    (A : P → E → ℂ) (H : P → E → ℝ)
    (hA : ∀ p, ContDiff ℝ ∞ (A p)) (hH : ∀ p, ContDiff ℝ ∞ (H p))
    {K : Set E} (hK : IsCompact K) (hs : ∀ p, tsupport (A p) ⊆ K)
    (hAj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p x, ‖iteratedFDeriv ℝ n (A p) x‖ ≤ B)
    (hHj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p x, ‖iteratedFDeriv ℝ n (H p) x‖ ≤ B)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α,
      (∫ ξ, ‖ξ‖ ^ k * ‖𝓕 (oscillatorySymbolSchwartz A H hA hH hK hs p α) ξ‖) ≤
        C * (1 + |α|) ^ (k + (volume : Measure E).integrablePower) :=
  exists_uniform_polynomial_fourier_moment
    (oscillatorySymbolSchwartz A H hA hH hK hs) hK
    (tsupport_oscillatorySymbolSchwartz_subset A H hA hH hK hs)
    (exists_uniform_oscillatorySymbol_jet_bound A H hA hH hAj hHj) k

end PlanarNikodym
