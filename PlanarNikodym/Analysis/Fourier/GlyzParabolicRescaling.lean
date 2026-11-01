import PlanarNikodym.Analysis.Fourier.GlyzParabolicSymbol
import PlanarNikodym.Analysis.Fourier.GlyzSmoothJetCoordinates
import PlanarNikodym.Analysis.Fourier.LocalAmplitudeExtension
import PlanarNikodym.Analysis.Fourier.UniformLowerDegreeReduction

/-! Exact operators associated to the compact parabolic symbols. The
original amplitude, input function, time Jacobian, and effective
frequency are all preserved. The normalized remainder parameter is
unrestricted, so the identities also apply before the terminal scale. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

def glyzCompactParabolicAmplitude {d n : ℕ}
    (A : GlyzParabolicSymbolVariables d n → ℂ)
    (H : GlyzParabolicSymbolVariables d n → ℝ)
    (q : ℝ × Aux (d + 2)) (δ : ℝ) (hδ : δ ≠ 0) (α : ℝ)
    (w : Aux (n + 1)) (τ η : ℝ) : ℂ :=
  let z := (((q, (lowerDegreeDilation n δ hδ).symm w), (τ, η)), δ)
  A z * Complex.exp (((α * H z : ℝ) : ℂ) * Complex.I)

theorem glyzCompactParabolicAmplitude_eq_actual {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (σ : Fin (n + 1) ↪ Fin (d + 2)) (a : Parameters 2 d × ℝ × ℝ → ℂ)
    {Φ : Parameters 2 d × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (A : GlyzParabolicSymbolVariables d n → ℂ)
    (H : GlyzParabolicSymbolVariables d n → ℝ)
    {K : Set ((ℝ × Aux (d + 2)) × Aux (n + 1))} {J : Set ℝ}
    (hsymbol : ∀ q y, (q, y) ∈ K → ∀ τ : ℝ, ∀ η ∈ J, ∀ δ ∈ Icc (0 : ℝ) 1, ∀ α : ℝ,
      A (((q, y), (τ, η)), δ) * Complex.exp
        (((α * H (((q, y), (τ, η)), δ) : ℝ) : ℂ) * Complex.I) =
          inverseChartTaylorAmplitude e σ a Φ ((((q, y), (τ, η)), α, δ)))
    (q : ℝ × Aux (d + 2)) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (r : ℝ) (w : Aux (n + 1)) (hw : (q, (lowerDegreeDilation n δ hδ.ne').symm w) ∈ K)
    (τ : ℝ) {η : ℝ} (hη : η ∈ J) :
    glyzCompactParabolicAmplitude A H q δ hδ.ne' (r * δ ^ (n + 1)) w τ η =
      actualTaylorAmplitude a Φ n r q.1 δ
        (parameterFrame d (q.2 + coordinateInsertion σ
          (e.symm (q, (lowerDegreeDilation n δ hδ.ne').symm w)).2)) τ η := by
  unfold glyzCompactParabolicAmplitude
  rw [hsymbol q _ hw τ η hη δ ⟨hδ.le, hδ1⟩]
  unfold inverseChartTaylorAmplitude
  exact rescaledTaylorAmplitude_eq_actualTaylorAmplitude a hΦ n _ r q.1 δ τ η

/-- The actual C∞ time-jet chart gives an exact Taylor normal form.
The anisotropic dilation produces the frequency factor δ^n. -/
theorem Family.timeTaylorEval_in_scaled_smooth_chart {d n : ℕ} (G : Family 2 d)
    (hm : n + 1 ≤ d + 2) (σ : Fin (n + 1) ↪ Fin (d + 2))
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (he : ∀ x, e x = (x.1, G.movingLowerJetMap hm σ x))
    (hΦ : ContDiff ℝ ∞ (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1))
    (q : ℝ × Aux (d + 2)) (δ : ℝ) (hδ : δ ≠ 0) (w : Aux (n + 1))
    (hw : (q, (lowerDegreeDilation n δ hδ).symm w) ∈ e.target) (τ : ℝ) :
    timeTaylorEval (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) n
      (parameterFrame d (q.2 + coordinateInsertion σ
        (e.symm (q, (lowerDegreeDilation n δ hδ).symm w)).2)) q.1 (q.1 + δ * τ) =
      δ ^ n * jetPolynomial w τ := by
  let y := (lowerDegreeDilation n δ hδ).symm w
  let z := e.symm (q, y)
  have hinv := e.right_inv hw
  rw [he] at hinv
  have hzq := congrArg (fun x : (ℝ × Aux (d + 2)) × Aux (n + 1) => x.1) hinv
  have hjet : G.lowerCinematicJetMap hm σ q.1 q.2 z.2 = y := by
    have hj := congrArg Prod.snd hinv
    change G.lowerCinematicJetMap hm σ z.1.1 z.1.2 z.2 = y at hj
    change z.1 = q at hzq
    rwa [hzq] at hj
  have hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) :=
    hΦ.comp (contDiff_snd.prodMk contDiff_fst)
  let p := parameterFrame d (q.2 + coordinateInsertion σ z.2)
  rw [timeTaylorEval_eq_jetPolynomial]
  have hcoeff : (fun i : Fin (n + 1) => iteratedDeriv i (fun s => G.γ s p) q.1) = y := by
    funext i
    have hi := congrFun hjet i
    change timeDerivative (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) i (q.1, p) = y i at hi
    rwa [timeDerivative_eq_iteratedDeriv_of_contDiff hG] at hi
  rw [hcoeff, add_sub_cancel_left, jetPolynomial_time_rescale n hδ]
  dsimp only [y]
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- Replace the true Taylor-corrected symbol in the exact original
extension by the constructed compact symbol, with no approximation. -/
theorem Family.timeSliceExtension_eq_compact_parabolic {d n : ℕ} (G : Family 2 d)
    (hm : n + 1 ≤ d + 2) (σ : Fin (n + 1) ↪ Fin (d + 2))
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (he : ∀ x, e x = (x.1, G.movingLowerJetMap hm σ x))
    (a : Parameters 2 d × ℝ × ℝ → ℂ)
    (hΦ : ContDiff ℝ ∞ (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1))
    (A : GlyzParabolicSymbolVariables d n → ℂ)
    (H : GlyzParabolicSymbolVariables d n → ℝ)
    {K : Set ((ℝ × Aux (d + 2)) × Aux (n + 1))} (hKT : K ⊆ e.target) {J : Set ℝ}
    (hsymbol : ∀ q y, (q, y) ∈ K → ∀ τ : ℝ, ∀ η ∈ J, ∀ δ ∈ Icc (0 : ℝ) 1, ∀ α : ℝ,
      A (((q, y), (τ, η)), δ) * Complex.exp
        (((α * H (((q, y), (τ, η)), δ) : ℝ) : ℂ) * Complex.I) =
          inverseChartTaylorAmplitude e σ a (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
            ((((q, y), (τ, η)), α, δ)))
    (h : ℝ × ℝ → ℂ) (hhJ : ∀ t η, η ∉ J → h (t, η) = 0)
    (q : ℝ × Aux (d + 2)) (r : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (w : Aux (n + 1)) (hw : (q, (lowerDegreeDilation n δ hδ.ne').symm w) ∈ K) :
    timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h r q.1 δ
      (parameterFrame d (q.2 + coordinateInsertion σ
        (e.symm (q, (lowerDegreeDilation n δ hδ.ne').symm w)).2)) =
      δ • polynomialExtension
        (glyzCompactParabolicAmplitude A H q δ hδ.ne' (r * δ ^ (n + 1)))
        (fun x => h (q.1 + δ * x.1, x.2)) (r * δ ^ n) w := by
  let y := (lowerDegreeDilation n δ hδ.ne').symm w
  let z := e.symm (q, y)
  have hy : (q, y) ∈ e.target := hKT hw
  have hinv := e.right_inv hy
  rw [he] at hinv
  have hzq : z.1 = q := congrArg Prod.fst hinv
  have hjet : G.lowerCinematicJetMap hm σ q.1 q.2 z.2 = y := by
    have hj := congrArg Prod.snd hinv
    change G.lowerCinematicJetMap hm σ z.1.1 z.1.2 z.2 = y at hj
    rwa [hzq] at hj
  have hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) :=
    hΦ.comp (contDiff_snd.prodMk contDiff_fst)
  let p := parameterFrame d (q.2 + coordinateInsertion σ z.2)
  have hphase (τ η : ℝ) :
      r * η * timeTaylorEval (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) n p q.1 (q.1 + δ * τ) =
        (r * δ ^ n) * η * jetPolynomial w τ := by
    rw [timeTaylorEval_eq_jetPolynomial]
    have hcoeff : (fun i : Fin (n + 1) => iteratedDeriv i (fun s => G.γ s p) q.1) = y := by
      funext i
      have hi := congrFun hjet i
      change timeDerivative (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) i (q.1, p) = y i at hi
      rwa [timeDerivative_eq_iteratedDeriv_of_contDiff hG] at hi
    rw [hcoeff, add_sub_cancel_left, jetPolynomial_time_rescale n hδ.ne']
    dsimp only [y]
    rw [ContinuousLinearEquiv.apply_symm_apply]
    ring
  rw [timeSliceExtension_eq_taylor _ a h n r q.1 hδ]
  congr 1
  unfold polynomialExtension
  apply integral_congr_ae
  filter_upwards [] with η
  by_cases hη : η ∈ J
  · apply integral_congr_ae
    filter_upwards [] with τ
    rw [glyzCompactParabolicAmplitude_eq_actual e σ a hΦ A H hsymbol q hδ hδ1 r w hw τ hη]
    unfold phaseOscillation
    have he := hphase τ η
    change r * η * _ = _ at he
    rw [he]
  · simp only [hhJ _ η hη, mul_zero, integral_zero]

/-- Both scale parameters are related exactly at every nonzero time
scale. This is the relative Fourier width used in the nonterminal step. -/
theorem glyz_parabolic_remainder_frequency_ratio (n : ℕ) {r δ : ℝ}
    (hr : r ≠ 0) (hδ : δ ≠ 0) :
    (r * δ ^ (n + 1)) / (r * δ ^ n) = δ := by
  rw [pow_succ]
  field_simp

end PlanarNikodym
