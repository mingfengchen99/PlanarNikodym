import PlanarNikodym.Analysis.Fourier.FourierReconstruction
import PlanarNikodym.Analysis.Maximal.MaximalMeasurability

/-! Sublinearity and measurable, finite-valued realization of the actual
frequency-localized maximal operator. The supremum remains the pointwise
supremum over every auxiliary parameter. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem FrequencyCutoff.band_add_integrable (L : FrequencyCutoff) (k : ℕ)
    {f g : Plane → ℂ} (hf : Integrable f) (hg : Integrable g) :
    L.band k (f + g) = L.band k f + L.band k g := by
  funext x
  unfold FrequencyCutoff.band
  simp only [Pi.add_apply, mul_add]
  exact integral_add
    (L.band_integrand_integrable k (p := 1) (q := ⊤) (memLp_one_iff_integrable.mpr hf) x)
    (L.band_integrand_integrable k (p := 1) (q := ⊤) (memLp_one_iff_integrable.mpr hg) x)

theorem FrequencyCutoff.band_congr_ae_input (L : FrequencyCutoff) (k : ℕ)
    {f g : Plane → ℂ} (hfg : f =ᵐ[volume] g) : L.band k f = L.band k g := by
  funext x
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

theorem FrequencyCutoff.band_enorm_le_e2 (L : FrequencyCutoff) (k : ℕ)
    {f : Plane → ℂ} (hf : Integrable f) (x : Plane) :
    ‖L.band k f x‖ₑ ≤ eLpNorm (L.bandKernel k) ⊤ volume * eLpNorm f 1 volume := by
  let K : Plane → ℂ := fun y => L.bandKernel k (x - y)
  have hK : MemLp K ⊤ volume := (L.bandKernel_memLp k ⊤).comp_measurePreserving
    (Measure.measurePreserving_sub_left volume x)
  calc
    _ ≤ ∫⁻ y, ‖K y * f y‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (K • f) 1 volume := by
      simp only [eLpNorm_one_eq_lintegral_enorm, smul_eq_mul, Pi.mul_apply]
    _ ≤ eLpNorm K ⊤ volume * eLpNorm f 1 volume :=
      eLpNorm_smul_le_mul_eLpNorm hf.aestronglyMeasurable hK.aestronglyMeasurable
    _ = _ := by
      congr 1
      exact eLpNorm_comp_measurePreserving (L.bandKernel_memLp k ⊤).aestronglyMeasurable
        (Measure.measurePreserving_sub_left volume x)

theorem Family.cutoffMaximal_band_ne_top_e2 {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (L : FrequencyCutoff) (k : ℕ) {f : Plane → ℂ} (hf : Integrable f)
    (z : Base 2) : G.cutoffMaximal χ (L.band k f) z ≠ ⊤ := by
  classical
  obtain ⟨x₀, hx₀⟩ := hχ.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  let T : Set ℝ := Prod.fst '' tsupport χ
  have hT : IsCompact T := hc.image continuous_fst
  let A : ℝ≥0∞ := volume T * ENNReal.ofReal ‖χ x₀‖ *
    eLpNorm (L.bandKernel k) ⊤ volume * eLpNorm f 1 volume
  have hA : A < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hT.measure_lt_top ENNReal.ofReal_lt_top)
      (L.bandKernel_memLp k ⊤).eLpNorm_lt_top)
    (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top
  apply ne_top_of_le_ne_top hA.ne
  apply iSup_le
  intro u
  calc
    _ ≤ ∫⁻ t, ‖(χ (t, (z, u)) : ℂ) * L.band k f (G.graphMap (z, u) t)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t, T.indicator (fun _ => ENNReal.ofReal ‖χ x₀‖ *
        eLpNorm (L.bandKernel k) ⊤ volume * eLpNorm f 1 volume) t := by
      apply lintegral_mono
      intro t
      by_cases ht : t ∈ T
      · rw [indicator_of_mem ht]
        dsimp only
        rw [enorm_mul, mul_assoc]
        apply mul_le_mul
        · rw [← ofReal_norm, Complex.norm_real]
          exact ENNReal.ofReal_le_ofReal (hx₀ (t, (z, u)))
        · exact L.band_enorm_le_e2 k hf _
        · exact zero_le
        · exact zero_le
      · rw [indicator_of_notMem ht]
        have hz : χ (t, (z, u)) = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => ht ⟨(t, (z, u)), h, rfl⟩)
        simp [hz]
    _ = A := by
      rw [lintegral_indicator_const hT.measurableSet]
      dsimp [A]
      ring

theorem Family.cutoffMaximal_band_subadditive_e2 {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (k : ℕ) {f g : Plane → ℂ}
    (hf : Integrable f) (hg : Integrable g) (z : Base 2) :
    G.cutoffMaximal χ (L.band k (f + g)) z ≤
      G.cutoffMaximal χ (L.band k f) z + G.cutoffMaximal χ (L.band k g) z := by
  rw [L.band_add_integrable k hf hg]
  apply iSup_le
  intro u
  rw [G.cutoffAverage_add_continuous χ hχ hc hγ (L.band_continuous k hf)
    (L.band_continuous k hg)]
  exact (enorm_add_le _ _).trans
    (add_le_add (le_iSup (fun u => ‖G.cutoffAverage χ (L.band k f) (z, u)‖ₑ) u)
      (le_iSup (fun u => ‖G.cutoffAverage χ (L.band k g) (z, u)‖ₑ) u))

/-- A complex-valued realization used only to invoke the generic norm
interpolation theorem; finiteness is proved above for all L¹ inputs. -/
def Family.bandMaximalComplex_e2 {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (L : FrequencyCutoff) (k : ℕ) (f : Plane → ℂ) (z : Base 2) : ℂ :=
  ((G.cutoffMaximal χ (L.band k f) z).toReal : ℂ)

theorem Family.bandMaximalComplex_e2_measurable {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (k : ℕ) {f : Plane → ℂ} (hf : Integrable f) :
    Measurable (G.bandMaximalComplex_e2 χ L k f) :=
  Complex.measurable_ofReal.comp
    ((G.measurable_cutoffMaximal
      (G.continuous_cutoffAverage hχ hc hγ (L.band_continuous k hf))).ennreal_toReal)

theorem Family.bandMaximalComplex_e2_enorm {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (L : FrequencyCutoff) (k : ℕ) {f : Plane → ℂ} (hf : Integrable f) (z : Base 2) :
    ‖G.bandMaximalComplex_e2 χ L k f z‖ₑ = G.cutoffMaximal χ (L.band k f) z := by
  rw [← ofReal_norm]
  simp only [bandMaximalComplex_e2, Complex.norm_real,
    Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal (G.cutoffMaximal_band_ne_top_e2 χ hχ hc L k hf z)

theorem Family.bandMaximalComplex_e2_eLpNorm {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (L : FrequencyCutoff) (k : ℕ) {f : Plane → ℂ} (hf : Integrable f) (p : ℝ≥0∞) :
    eLpNorm (G.bandMaximalComplex_e2 χ L k f) p volume =
      eLpNorm (G.cutoffMaximal χ (L.band k f)) p volume := by
  apply eLpNorm_congr_enorm_ae
  filter_upwards [] with z
  simpa only [enorm_eq_self] using G.bandMaximalComplex_e2_enorm χ hχ hc L k hf z

theorem Family.bandMaximalComplex_e2_subadditive {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (k : ℕ) {f g : Plane → ℂ}
    (hf : Integrable f) (hg : Integrable g) (z : Base 2) :
    ‖G.bandMaximalComplex_e2 χ L k (f + g) z‖ ≤
      ‖G.bandMaximalComplex_e2 χ L k f z‖ + ‖G.bandMaximalComplex_e2 χ L k g z‖ := by
  simp only [bandMaximalComplex_e2, Complex.norm_real,
    Real.norm_of_nonneg ENNReal.toReal_nonneg]
  rw [← ENNReal.toReal_add (G.cutoffMaximal_band_ne_top_e2 χ hχ hc L k hf z)
    (G.cutoffMaximal_band_ne_top_e2 χ hχ hc L k hg z)]
  exact ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨G.cutoffMaximal_band_ne_top_e2 χ hχ hc L k hf z,
      G.cutoffMaximal_band_ne_top_e2 χ hχ hc L k hg z⟩)
    (G.cutoffMaximal_band_subadditive_e2 χ hχ hc hγ L k hf hg z)

end PlanarNikodym
