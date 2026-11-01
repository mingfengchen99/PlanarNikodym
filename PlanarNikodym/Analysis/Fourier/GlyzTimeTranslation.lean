import PlanarNikodym.Analysis.Fourier.GlyzRawKernel
import Mathlib.MeasureTheory.Group.Integral

/-! Fixed translations of the input time coordinate preserve the
cinematic determinant and the original extension exactly. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

def Family.glyzTimeTranslate {d : ℕ} (G : Family 2 d) (s : ℝ) : Family 2 d :=
  { G with γ := fun t p => G.γ (t + s) p }

def glyzTimeTranslateAmplitude {P : Type} (a : P × Plane → ℂ) (s : ℝ) :
    P × Plane → ℂ := fun z => a (z.1, z.2.1 + s, z.2.2)

def glyzTimeTranslateInput (g : Plane → ℂ) (s : ℝ) : Plane → ℂ :=
  fun y => g (y.1 + s, y.2)

theorem timeDerivative_comp_timeTranslate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × E → ℝ) (s : ℝ) (j : ℕ) :
    timeDerivative (fun x => f (x + (s, 0))) j =
      fun x => timeDerivative f j (x + (s, 0)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext x
    simp only [timeDerivative, ih, fderiv_comp_add_right]

@[simp] theorem Family.cinematicDet_glyzTimeTranslate {d : ℕ}
    (G : Family 2 d) (s : ℝ) (x : ℝ × Parameters 2 d) :
    (G.glyzTimeTranslate s).cinematicDet x = G.cinematicDet (x.1 + s, x.2) := by
  apply congrArg Matrix.det
  funext i j
  have hcol : (G.glyzTimeTranslate s).parameterColumn j =
      fun y => G.parameterColumn j (y + (s, 0)) := by
    funext y
    unfold Family.parameterColumn Family.glyzTimeTranslate
    have he : (fun z : ℝ × Parameters 2 d => G.γ (z.1 + s) z.2) =
        fun z => (fun w : ℝ × Parameters 2 d => G.γ w.1 w.2) (z + (s, 0)) := by
      funext z
      simp only [Prod.fst_add, Prod.snd_add, add_zero]
    rw [he]
    exact congrArg (fun L : (ℝ × Parameters 2 d) →L[ℝ] ℝ =>
      L (0, parameterFrame d (Pi.single j 1)))
      (fderiv_comp_add_right (𝕜 := ℝ)
        (f := fun z : ℝ × Parameters 2 d => G.γ z.1 z.2) (x := y) (s, 0))
  change timeDerivative ((G.glyzTimeTranslate s).parameterColumn j) i x = _
  rw [hcol, timeDerivative_comp_timeTranslate]
  change timeDerivative (G.parameterColumn j) i (x.1 + s, x.2 + 0) =
    timeDerivative (G.parameterColumn j) i (x.1 + s, x.2)
  rw [add_zero]

theorem Family.contDiff_glyzTimeTranslate {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (s : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => (G.glyzTimeTranslate s).γ x.1 x.2) :=
  hG.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)

theorem contDiff_glyzTimeTranslateAmplitude {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {a : P × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (s : ℝ) :
    ContDiff ℝ ∞ (glyzTimeTranslateAmplitude a s) :=
  ha.comp (contDiff_fst.prodMk
    ((contDiff_snd.fst.add contDiff_const).prodMk contDiff_snd.snd))

theorem hasCompactSupport_glyzTimeTranslateAmplitude {P : Type}
    [NormedAddCommGroup P] {a : P × Plane → ℂ} (ha : HasCompactSupport a) (s : ℝ) :
    HasCompactSupport (glyzTimeTranslateAmplitude a s) := by
  have he : glyzTimeTranslateAmplitude a s =
      a ∘ Homeomorph.addRight ((0 : P), s, (0 : ℝ)) := by
    funext z
    change a (z.1, z.2.1 + s, z.2.2) = a (z.1 + 0, z.2.1 + s, z.2.2 + 0)
    simp only [add_zero]
  rw [he]
  exact ha.comp_homeomorph (Homeomorph.addRight ((0 : P), s, (0 : ℝ)))

theorem glyzRawExtension_timeTranslate {P : Type} (Φ : P × ℝ → ℝ)
    (a : P × Plane → ℂ) (g : Plane → ℂ) (s r : ℝ) :
    glyzRawExtension (fun z => Φ (z.1, z.2 + s))
      (glyzTimeTranslateAmplitude a s) (glyzTimeTranslateInput g s) r =
      glyzRawExtension Φ a g r := by
  funext p
  unfold glyzRawExtension
  apply integral_congr_ae
  filter_upwards [] with η
  exact integral_add_right_eq_self
    (fun t => phaseOscillation (fun u => Φ (p, u)) (r * η) t *
      a (p, t, η) * g (t, η)) s

theorem integrable_glyzTimeTranslateInput {g : Plane → ℂ}
    (hg : Integrable g) (s : ℝ) : Integrable (glyzTimeTranslateInput g s) := by
  have h := (memLp_one_iff_integrable.mpr hg).comp_measurePreserving
    (measurePreserving_add_right volume (s, (0 : ℝ)))
  apply memLp_one_iff_integrable.mp
  have he : glyzTimeTranslateInput g s = g ∘ (fun y => y + (s, (0 : ℝ))) := by
    funext y
    change g (y.1 + s, y.2) = g (y.1 + s, y.2 + 0)
    rw [add_zero]
  rwa [he]

theorem memLp_glyzTimeTranslateInput {g : Plane → ℂ} {p : ℝ≥0∞}
    (hg : MemLp g p) (s : ℝ) : MemLp (glyzTimeTranslateInput g s) p := by
  have he : glyzTimeTranslateInput g s = g ∘ (fun y => y + (s, (0 : ℝ))) := by
    funext y
    change g (y.1 + s, y.2) = g (y.1 + s, y.2 + 0)
    rw [add_zero]
  rw [he]
  exact hg.comp_measurePreserving (measurePreserving_add_right volume (s, (0 : ℝ)))

theorem lintegral_enorm_glyzTimeTranslateInput (g : Plane → ℂ) (s : ℝ) :
    (∫⁻ y, ‖glyzTimeTranslateInput g s y‖ₑ) = ∫⁻ y, ‖g y‖ₑ := by
  have he (y : Plane) : glyzTimeTranslateInput g s y = g (y + (s, 0)) := by
    change g (y.1 + s, y.2) = g (y.1 + s, y.2 + 0)
    rw [add_zero]
  simp_rw [he]
  exact lintegral_add_right_eq_self (μ := volume) (fun y : Plane => ‖g y‖ₑ) (s, (0 : ℝ))

theorem Family.exists_glyzTimeTranslate_regular_support {d : ℕ}
    (G : Family 2 d) {a : Parameters 2 d × Plane → ℂ}
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ p t η, a (p, t, η) ≠ 0 → (t, p) ∈ K) (s : ℝ) :
    ∃ K' : Set (ℝ × Parameters 2 d), IsCompact K' ∧
      (∀ x ∈ K', (G.glyzTimeTranslate s).cinematicDet x ≠ 0) ∧
      ∀ p t η, glyzTimeTranslateAmplitude a s (p, t, η) ≠ 0 → (t, p) ∈ K' := by
  let K' := (fun x : ℝ × Parameters 2 d => (x.1 - s, x.2)) '' K
  refine ⟨K', hK.image ((continuous_fst.sub continuous_const).prodMk continuous_snd),
    ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    simpa only [Family.cinematicDet_glyzTimeTranslate, sub_add_cancel] using hdet x hx
  · intro p t η hn
    exact ⟨(t + s, p), has p (t + s) η hn, by simp only [add_sub_cancel_right]⟩

end PlanarNikodym
