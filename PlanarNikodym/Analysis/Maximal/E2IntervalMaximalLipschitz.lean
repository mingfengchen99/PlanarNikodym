import PlanarNikodym.Analysis.Maximal.E2IntervalMaximal

/-! Actual norm-difference control for Definition 1.3 on a compact
parameter set, before passing to equivalence classes in Lᵖ. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem Family.intervalMaximal_e2_neg {d : ℕ} (G : Family 2 d)
    (K : Set (Parameters 2 d)) (f : Plane → ℂ) :
    G.intervalMaximal_e2 K (-f) = G.intervalMaximal_e2 K f := by
  funext z
  unfold intervalMaximal_e2
  apply iSup_congr
  intro u
  apply iSup_congr
  intro _
  simp only [intervalAverage_e2, Pi.neg_apply, integral_neg, enorm_neg]

theorem Family.intervalMaximal_e2_add_le {d : ℕ} (G : Family 2 d) (hG : G.IsSmooth)
    (K : Set (Parameters 2 d)) (hKW : K ⊆ G.W)
    {f g : Plane → ℂ} (hf : Continuous f) (hg : Continuous g)
    {Bf Bg : ℝ} (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ x, ‖g x‖ ≤ Bg) (z : Base 2) :
    G.intervalMaximal_e2 K (f + g) z ≤ G.intervalMaximal_e2 K f z + G.intervalMaximal_e2 K g z := by
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  have he : G.intervalAverage_e2 (f + g) (z, u) =
      G.intervalAverage_e2 f (z, u) + G.intervalAverage_e2 g (z, u) := by
    unfold intervalAverage_e2
    simp only [Pi.add_apply]
    exact integral_add (G.intervalIntegrand_e2_integrable hG hf hBf (hKW hu))
      (G.intervalIntegrand_e2_integrable hG hg hBg (hKW hu))
  rw [he]
  exact (enorm_add_le _ _).trans (add_le_add
    (le_iSup_of_le u (le_iSup_of_le hu le_rfl)) (le_iSup_of_le u (le_iSup_of_le hu le_rfl)))

def Family.intervalMaximalComplex_e2 {d : ℕ} (G : Family 2 d) (K : Set (Parameters 2 d))
    (f : Plane → ℂ) (z : Base 2) : ℂ := ((G.intervalMaximal_e2 K f z).toReal : ℂ)

@[simp] theorem Family.intervalMaximalComplex_e2_zero {d : ℕ} (G : Family 2 d)
    (K : Set (Parameters 2 d)) : G.intervalMaximalComplex_e2 K 0 = 0 := by
  funext z
  simp [intervalMaximalComplex_e2, intervalMaximal_e2, intervalAverage_e2]

theorem Family.intervalMaximalComplex_e2_measurable {d : ℕ} (G : Family 2 d)
    (hG : G.IsSmooth) (K : Set (Parameters 2 d)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    {f : Plane → ℂ} (hf : Continuous f) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    Measurable (G.intervalMaximalComplex_e2 K f) :=
  Complex.measurable_ofReal.comp
    ((G.measurable_intervalMaximal_e2 hG K hK hKW hf hB).ennreal_toReal)

theorem Family.intervalMaximalComplex_e2_enorm {d : ℕ} (G : Family 2 d)
    (K : Set (Parameters 2 d)) {f : Plane → ℂ} {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (z : Base 2) :
    ‖G.intervalMaximalComplex_e2 K f z‖ₑ = G.intervalMaximal_e2 K f z := by
  rw [← ofReal_norm]
  simp only [intervalMaximalComplex_e2, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal (G.intervalMaximal_e2_ne_top K hB z)

theorem Family.intervalMaximalComplex_e2_eLpNorm {d : ℕ} (G : Family 2 d)
    (K : Set (Parameters 2 d)) {f : Plane → ℂ} {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (p : ℝ≥0∞) :
    eLpNorm (G.intervalMaximalComplex_e2 K f) p volume = eLpNorm (G.intervalMaximal_e2 K f) p volume := by
  apply eLpNorm_congr_enorm_ae
  filter_upwards [] with z
  simpa only [enorm_eq_self] using G.intervalMaximalComplex_e2_enorm K hB z

theorem Family.intervalMaximalComplex_e2_norm_sub_le {d : ℕ} (G : Family 2 d)
    (hG : G.IsSmooth) (K : Set (Parameters 2 d)) (hKW : K ⊆ G.W)
    {f g : Plane → ℂ} (hf : Continuous f) (hg : Continuous g)
    {Bf Bg : ℝ} (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ x, ‖g x‖ ≤ Bg) (z : Base 2) :
    ‖G.intervalMaximalComplex_e2 K f z - G.intervalMaximalComplex_e2 K g z‖ ≤
      ‖G.intervalMaximalComplex_e2 K (f - g) z‖ := by
  have hBd : ∀ x, ‖(f - g) x‖ ≤ Bf + Bg := fun x =>
    (norm_sub_le (f x) (g x)).trans (add_le_add (hBf x) (hBg x))
  have hMf := G.intervalMaximal_e2_ne_top K hBf z
  have hMg := G.intervalMaximal_e2_ne_top K hBg z
  have hMd := G.intervalMaximal_e2_ne_top K hBd z
  have hfg : G.intervalMaximal_e2 K f z ≤ G.intervalMaximal_e2 K (f - g) z + G.intervalMaximal_e2 K g z := by
    have hh := G.intervalMaximal_e2_add_le hG K hKW (f := f - g) (g := g) (hf.sub hg) hg hBd hBg z
    simpa only [sub_add_cancel] using hh
  have hgf : G.intervalMaximal_e2 K g z ≤ G.intervalMaximal_e2 K (f - g) z + G.intervalMaximal_e2 K f z := by
    have hBdf : ∀ x, ‖(g - f) x‖ ≤ Bg + Bf := fun x =>
      (norm_sub_le (g x) (f x)).trans (add_le_add (hBg x) (hBf x))
    have hh := G.intervalMaximal_e2_add_le hG K hKW (f := g - f) (g := f) (hg.sub hf) hf hBdf hBf z
    rw [sub_add_cancel] at hh
    have he : g - f = -(f - g) := by abel
    rw [he, G.intervalMaximal_e2_neg] at hh
    exact hh
  have hrfg := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hMd, hMg⟩) hfg
  have hrgf := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hMd, hMf⟩) hgf
  rw [ENNReal.toReal_add hMd hMg] at hrfg
  rw [ENNReal.toReal_add hMd hMf] at hrgf
  simp only [intervalMaximalComplex_e2, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end PlanarNikodym
