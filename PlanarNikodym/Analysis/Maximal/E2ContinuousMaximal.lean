import PlanarNikodym.Analysis.Maximal.E2BandSublinearity

/-! The original, non-frequency-localized maximal operator on continuous
bounded tests. Its norm difference is controlled by the maximal operator
of the difference, which supplies the Lipschitz extension to Lᵖ. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem Family.cutoffMaximal_ne_top_of_bounded_e2 {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {f : Plane → ℂ} {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (z : Base 2) :
    G.cutoffMaximal χ f z ≠ ⊤ := by
  classical
  obtain ⟨x₀, hx₀⟩ := hχ.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  let T : Set ℝ := Prod.fst '' tsupport χ
  have hT : IsCompact T := hc.image continuous_fst
  let A : ℝ≥0∞ := volume T * ENNReal.ofReal ‖χ x₀‖ * ENNReal.ofReal B
  have hA : A < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top hT.measure_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top
  apply ne_top_of_le_ne_top hA.ne
  apply iSup_le
  intro u
  calc
    _ ≤ ∫⁻ t, ‖(χ (t, (z, u)) : ℂ) * f (G.graphMap (z, u) t)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t, T.indicator (fun _ => ENNReal.ofReal ‖χ x₀‖ * ENNReal.ofReal B) t := by
      apply lintegral_mono
      intro t
      by_cases ht : t ∈ T
      · rw [indicator_of_mem ht]
        dsimp only
        rw [enorm_mul]
        apply mul_le_mul _ _ zero_le zero_le
        · rw [← ofReal_norm, Complex.norm_real]
          exact ENNReal.ofReal_le_ofReal (hx₀ (t, (z, u)))
        · rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hB _)
      · rw [indicator_of_notMem ht]
        have hz : χ (t, (z, u)) = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => ht ⟨(t, (z, u)), h, rfl⟩)
        simp [hz]
    _ = A := by
      rw [lintegral_indicator_const hT.measurableSet]
      dsimp [A]
      ring

theorem Family.cutoffMaximal_neg_e2 {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (f : Plane → ℂ) : G.cutoffMaximal χ (-f) = G.cutoffMaximal χ f := by
  funext z
  change (⨆ u : Aux d, ‖G.cutoffAverage χ (-f) (z, u)‖ₑ) =
    ⨆ u : Aux d, ‖G.cutoffAverage χ f (z, u)‖ₑ
  apply iSup_congr
  intro u
  have he : G.cutoffAverage χ (-f) (z, u) = -G.cutoffAverage χ f (z, u) := by
    unfold cutoffAverage
    simp only [Pi.neg_apply, mul_neg, integral_neg]
  rw [he, enorm_neg]

theorem Family.cutoffMaximal_add_le_e2 {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f g : Plane → ℂ} (hf : Continuous f) (hg : Continuous g) (z : Base 2) :
    G.cutoffMaximal χ (f + g) z ≤ G.cutoffMaximal χ f z + G.cutoffMaximal χ g z := by
  apply iSup_le
  intro u
  rw [G.cutoffAverage_add_continuous χ hχ hc hγ hf hg]
  exact (enorm_add_le _ _).trans
    (add_le_add (le_iSup (fun u => ‖G.cutoffAverage χ f (z, u)‖ₑ) u)
      (le_iSup (fun u => ‖G.cutoffAverage χ g (z, u)‖ₑ) u))

def Family.cutoffMaximalComplex_e2 {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (f : Plane → ℂ) (z : Base 2) : ℂ :=
  ((G.cutoffMaximal χ f z).toReal : ℂ)

@[simp] theorem Family.cutoffMaximalComplex_e2_zero {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) : G.cutoffMaximalComplex_e2 χ 0 = 0 := by
  have havg : G.cutoffAverage χ 0 = 0 := by
    funext q
    simp [Family.cutoffAverage]
  funext z
  simp [Family.cutoffMaximalComplex_e2, Family.cutoffMaximal, havg]

theorem Family.cutoffMaximalComplex_e2_measurable {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : Continuous f) : Measurable (G.cutoffMaximalComplex_e2 χ f) :=
  Complex.measurable_ofReal.comp
    ((G.measurable_cutoffMaximal (G.continuous_cutoffAverage hχ hc hγ hf)).ennreal_toReal)

theorem Family.cutoffMaximalComplex_e2_enorm {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {f : Plane → ℂ} {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (z : Base 2) :
    ‖G.cutoffMaximalComplex_e2 χ f z‖ₑ = G.cutoffMaximal χ f z := by
  rw [← ofReal_norm]
  simp only [cutoffMaximalComplex_e2, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal (G.cutoffMaximal_ne_top_of_bounded_e2 χ hχ hc hB z)

theorem Family.cutoffMaximalComplex_e2_eLpNorm {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {f : Plane → ℂ} {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (p : ℝ≥0∞) :
    eLpNorm (G.cutoffMaximalComplex_e2 χ f) p volume = eLpNorm (G.cutoffMaximal χ f) p volume := by
  apply eLpNorm_congr_enorm_ae
  filter_upwards [] with z
  simpa only [enorm_eq_self] using G.cutoffMaximalComplex_e2_enorm χ hχ hc hB z

theorem Family.cutoffMaximalComplex_e2_norm_sub_le {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f g : Plane → ℂ} (hf : Continuous f) (hg : Continuous g)
    {Bf Bg : ℝ} (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ x, ‖g x‖ ≤ Bg) (z : Base 2) :
    ‖G.cutoffMaximalComplex_e2 χ f z - G.cutoffMaximalComplex_e2 χ g z‖ ≤
      ‖G.cutoffMaximalComplex_e2 χ (f - g) z‖ := by
  have hBd : ∀ x, ‖(f - g) x‖ ≤ Bf + Bg := fun x =>
    (norm_sub_le (f x) (g x)).trans (add_le_add (hBf x) (hBg x))
  have hMf := G.cutoffMaximal_ne_top_of_bounded_e2 χ hχ hc hBf z
  have hMg := G.cutoffMaximal_ne_top_of_bounded_e2 χ hχ hc hBg z
  have hMd := G.cutoffMaximal_ne_top_of_bounded_e2 χ hχ hc hBd z
  have hfg : G.cutoffMaximal χ f z ≤ G.cutoffMaximal χ (f - g) z + G.cutoffMaximal χ g z := by
    have hh := G.cutoffMaximal_add_le_e2 χ hχ hc hγ (f := f - g) (g := g) (hf.sub hg) hg z
    simpa only [sub_add_cancel] using hh
  have hgf : G.cutoffMaximal χ g z ≤ G.cutoffMaximal χ (f - g) z + G.cutoffMaximal χ f z := by
    have hh := G.cutoffMaximal_add_le_e2 χ hχ hc hγ (f := g - f) (g := f) (hg.sub hf) hf z
    rw [sub_add_cancel] at hh
    have he : g - f = -(f - g) := by abel
    rw [he, G.cutoffMaximal_neg_e2] at hh
    exact hh
  have hrfg := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hMd, hMg⟩) hfg
  have hrgf := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hMd, hMf⟩) hgf
  rw [ENNReal.toReal_add hMd hMg] at hrfg
  rw [ENNReal.toReal_add hMd hMf] at hrgf
  simp only [cutoffMaximalComplex_e2, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end PlanarNikodym
