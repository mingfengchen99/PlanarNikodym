import PlanarNikodym.Analysis.Fourier.GlyzNormalizedDyadicInput
import PlanarNikodym.Analysis.Fourier.GlyzRawKernel

/-! Exact normalization and reconstruction of the actual sharp dyadic
input in the raw extension. No extra time window is introduced. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal ContDiff
namespace PlanarNikodym

def glyzDenormalizedInput (c δ : ℝ) (h : Plane → ℂ) (y : Plane) : ℂ :=
  h ((y.1 - c) / δ, y.2)

theorem glyz_normalize_denormalize (h : Plane → ℂ) (c : ℝ) {δ : ℝ} (hδ : δ ≠ 0) :
    glyzDenormalizedInput c δ h ∘ timeDataRescaling c δ = h := by
  funext y
  simp only [Function.comp_apply, glyzDenormalizedInput, timeDataRescaling]
  congr 1
  ext <;> simp [hδ]

theorem glyz_denormalize_normalize (h : Plane → ℂ) (c : ℝ) {δ : ℝ} (hδ : δ ≠ 0) :
    glyzDenormalizedInput c δ (h ∘ timeDataRescaling c δ) = h := by
  funext y
  simp only [Function.comp_apply, glyzDenormalizedInput, timeDataRescaling]
  congr 1
  apply Prod.ext
  · dsimp
    field_simp
    ring
  · rfl

theorem glyzDenormalizedInput_eq_rescaling (h : Plane → ℂ) (c δ : ℝ) :
    glyzDenormalizedInput c δ h = h ∘ timeDataRescaling (-c / δ) δ⁻¹ := by
  funext y
  dsimp [glyzDenormalizedInput, timeDataRescaling]
  apply congrArg h
  apply Prod.ext
  · dsimp; ring
  · rfl

theorem integrable_glyzDenormalizedInput {h : Plane → ℂ} (hh : Integrable h)
    (c : ℝ) {δ : ℝ} (hδ : δ ≠ 0) : Integrable (glyzDenormalizedInput c δ h) := by
  rw [glyzDenormalizedInput_eq_rescaling]
  exact integrable_glyzTimeDataRescaling hh _ (inv_ne_zero hδ)

theorem glyzDenormalizedInput_integral_norm {h : Plane → ℂ} (hh : Integrable h)
    (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ y, ‖glyzDenormalizedInput c δ h y‖) = δ * ∫ y, ‖h y‖ := by
  rw [glyzDenormalizedInput_eq_rescaling]
  simpa only [inv_inv, Function.comp_apply] using
    integral_norm_timeDataRescaling hh (-c / δ) (inv_pos.mpr hδ)

theorem support_glyzDenormalizedInput {h : Plane → ℂ} {J : Set ℝ}
    (hh : Function.support h ⊆ Icc (0 : ℝ) 1 ×ˢ J) (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Function.support (glyzDenormalizedInput c δ h) ⊆ Icc c (c + δ) ×ˢ J := by
  intro y hy
  have hs := hh (show ((y.1 - c) / δ, y.2) ∈ Function.support h from hy)
  refine ⟨⟨?_, ?_⟩, hs.2⟩
  · have hz := (le_div_iff₀ hδ).mp hs.1.1
    linarith
  · have hz := (div_le_iff₀ hδ).mp hs.1.2
    linarith

theorem glyzDenormalizedInput_normalizedDyadicInput (g : Plane → ℂ) (n q i j : ℕ) :
    glyzDenormalizedInput (glyzDyadicLeft n i) (glyzDyadicScale n)
      (glyzNormalizedDyadicInput n q i j g) = glyzDyadicInput (n + q) (i * 2 ^ q + j) g :=
  glyz_denormalize_normalize _ _ (glyzDyadicScale_pos n).ne'

theorem support_glyzNormalizedDyadicInput_unit {g : Plane → ℂ} {J : Set ℝ}
    (hs : Function.support g ⊆ {y | y.2 ∈ J}) (n q i j : ℕ) (hj : j < 2 ^ q) :
    Function.support (glyzNormalizedDyadicInput n q i j g) ⊆ Icc (0 : ℝ) 1 ×ˢ J := by
  intro y hy
  have h := support_glyzNormalizedDyadicInput hs n q i j hy
  exact ⟨glyzDyadicInterval_subset_unit hj ⟨h.1.1, h.1.2.le⟩, h.2⟩

theorem support_glyzDyadicInput_child_parent {g : Plane → ℂ} {J : Set ℝ}
    (hs : Function.support g ⊆ {y | y.2 ∈ J}) (n q i j : ℕ) (hj : j < 2 ^ q) :
    Function.support (glyzDyadicInput (n + q) (i * 2 ^ q + j) g) ⊆
      Icc (glyzDyadicLeft n i) (glyzDyadicLeft n i + glyzDyadicScale n) ×ˢ J := by
  rw [← glyzDenormalizedInput_normalizedDyadicInput g n q i j]
  exact support_glyzDenormalizedInput (support_glyzNormalizedDyadicInput_unit hs n q i j hj)
    _ (glyzDyadicScale_pos n)

/-- Raw extension and compact-kernel dyadic energy refer to exactly the
same actual input, including its sharp interval endpoints. -/
theorem glyzRawExtension_dyadicInput_eq_piece {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a : P × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {g : Plane → ℂ} (hg : Integrable g) (r : ℝ) (n i : ℕ) (p : P) :
    glyzRawExtension Φ a (glyzDyadicInput n i g) r p =
      glyzDyadicKernelPiece (glyzRawKernel Φ a r) g n i p :=
  glyzRawExtension_eq_compactKernel hΦ ha hc (integrable_glyzDyadicInput hg n i) r p

/-- The actual compact symbol represents normalized data exactly, with
its denormalized original data on the raw-operator side. -/
theorem Family.compact_parabolic_eq_output_cutoff_denormalized {d n : ℕ} (G : Family 2 d)
    (hm : n + 1 ≤ d + 2) (σ : Fin (n + 1) ↪ Fin (d + 2))
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (he : ∀ x, e x = (x.1, G.movingLowerJetMap hm σ x))
    (a : Parameters 2 d × ℝ × ℝ → ℂ)
    (hΦ : ContDiff ℝ ∞ (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1))
    (ρ : ((ℝ × Aux (d + 2)) × Aux (n + 1)) → ℝ) (hρT : tsupport ρ ⊆ e.target)
    (A : GlyzParabolicSymbolVariables d n → ℂ) (H : GlyzParabolicSymbolVariables d n → ℝ)
    {J : Set ℝ}
    (hsymbol : ∀ q y, ∀ τ ∈ Icc (0 : ℝ) 1, ∀ η ∈ J, ∀ δ ∈ Icc (0 : ℝ) 1, ∀ α : ℝ,
      A (((q, y), (τ, η)), δ) * Complex.exp
        (((α * H (((q, y), (τ, η)), δ) : ℝ) : ℂ) * Complex.I) =
        (ρ (q, y) : ℂ) * (glyzRawInverseChartBaseSymbol e σ a (((q, y), (τ, η)), δ) *
          Complex.exp (((α * glyzInverseChartRemainderProfile e σ
            (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
            (((q, y), (τ, η)), δ) : ℝ) : ℂ) * Complex.I)))
    (h : ℝ × ℝ → ℂ)
    (q : ℝ × Aux (d + 2)) (r : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hh : Function.support h ⊆ Icc (0 : ℝ) 1 ×ˢ J)
    (w : Aux (n + 1)) :
    δ • polynomialExtension
      (glyzCompactParabolicAmplitude A H q δ hδ.ne' (r * δ ^ (n + 1)))
      h (r * δ ^ n) w =
      (ρ (q, (lowerDegreeDilation n δ hδ.ne').symm w) : ℂ) *
        glyzRawExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a (glyzDenormalizedInput q.1 δ h) r
          (parameterFrame d (q.2 + coordinateInsertion σ
            (e.symm (q, (lowerDegreeDilation n δ hδ.ne').symm w)).2)) := by
  have hb := G.compact_parabolic_eq_output_cutoff_rawExtension hm σ e he a hΦ ρ hρT A H
    hsymbol (glyzDenormalizedInput q.1 δ h) q r hδ hδ1
    (support_glyzDenormalizedInput hh q.1 hδ) w
  have hi : (fun x : Plane => glyzDenormalizedInput q.1 δ h (q.1 + δ * x.1, x.2)) = h :=
    glyz_normalize_denormalize h q.1 hδ.ne'
  simpa only [hi] using hb

/-- Exact reconstruction of the original raw parent extension. -/
theorem glyzRawExtension_dyadicInput_refine {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a : P × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {g : Plane → ℂ} (hg : Integrable g) (r : ℝ) (n q i : ℕ) (p : P) :
    glyzRawExtension Φ a (glyzDyadicInput n i g) r p =
      ∑ j ∈ Finset.range (2 ^ q),
        glyzRawExtension Φ a (glyzDyadicInput (n + q) (i * 2 ^ q + j) g) r p := by
  rw [glyzRawExtension_eq_compactKernel hΦ ha hc (integrable_glyzDyadicInput hg n i)]
  rw [glyz_compactKernel_dyadicInput_refine hg (contDiff_glyzRawKernel hΦ ha r)
    (hasCompactSupport_glyzRawKernel Φ hc r)]
  apply Finset.sum_congr rfl
  intro j hj
  exact (glyzRawExtension_eq_compactKernel hΦ ha hc (integrable_glyzDyadicInput hg _ _) r p).symm

end PlanarNikodym
