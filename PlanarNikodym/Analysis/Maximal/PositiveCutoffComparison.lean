import PlanarNikodym.Analysis.Maximal.MaximalMeasurability

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym.Family
variable {d : ℕ} (G : Family 2 d)

theorem cutoffAverage_real (χ : Cutoff d) (f : Plane → ℝ) (p : Parameters 2 d) :
    G.cutoffAverage χ (fun x => (f x : ℂ)) p =
      ((∫ t : ℝ, χ (t, p) * f (G.graphMap p t) : ℝ) : ℂ) := by
  simp only [cutoffAverage, ← Complex.ofReal_mul, integral_complex_ofReal]

/-- A nonnegative cutoff which is at least one on the original interval
controls its nonnegative average, including all contributions outside I. -/
theorem positiveAverage_le_cutoffAverage {χ : Cutoff d}
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (hχ0 : ∀ x, 0 ≤ χ x) {f : Plane → ℝ} (hf : Continuous f)
    (h0 : ∀ x, 0 ≤ f x) (p : Parameters 2 d)
    (hχ1 : ∀ t ∈ G.I.carrier, 1 ≤ χ (t, p)) :
    G.positiveAverage (fun x => ENNReal.ofReal (f x)) p ≤
      ‖G.cutoffAverage χ (fun x => (f x : ℂ)) p‖ₑ := by
  let H : ℝ → ℝ := fun t => χ (t, p) * f (G.graphMap p t)
  have hH : Continuous H := by
    have h := Complex.continuous_re.comp ((G.continuous_cutoffIntegrand hχ hγ
      (Complex.continuous_ofReal.comp hf)).comp
      (continuous_id.prodMk (continuous_const (y := p))))
    simpa only [H, graphMap, Function.comp_def, id_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using h
  have hHc : HasCompactSupport H := by
    apply HasCompactSupport.intro (hc.image continuous_fst)
    intro t ht
    have hz : χ (t, p) = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => ht ⟨(t, p), h, rfl⟩)
    simp [H, hz]
  have hi : Integrable H := hH.integrable_of_hasCompactSupport hHc
  have hH0 (t : ℝ) : 0 ≤ H t := mul_nonneg (hχ0 _) (h0 _)
  have he : ‖G.cutoffAverage χ (fun x => (f x : ℂ)) p‖ₑ =
      ∫⁻ t : ℝ, ENNReal.ofReal (H t) := by
    rw [G.cutoffAverage_real, ← ofReal_norm, Complex.norm_real,
      Real.norm_of_nonneg (integral_nonneg hH0)]
    exact ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hH0)
  rw [he]
  calc
    _ ≤ ∫⁻ t in G.I.carrier, ENNReal.ofReal (H t) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      apply ENNReal.ofReal_le_ofReal
      dsimp [H]
      nlinarith [h0 (G.graphMap p t), hχ1 t ht]
    _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl

theorem positiveMaximal_le_cutoffMaximal (U : Set (Parameters 2 d))
    {χ : Cutoff d} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ t ∈ G.I.carrier, ∀ p ∈ U, 1 ≤ χ (t, p))
    {f : Plane → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x) :
    G.positiveMaximal U (fun x => ENNReal.ofReal (f x)) ≤
      G.cutoffMaximal χ (fun x => (f x : ℂ)) := by
  intro z
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  exact (G.positiveAverage_le_cutoffAverage hχ hc hγ hχ0 hf h0 (z, u)
    (fun t ht => hχ1 t ht (z, u) hu)).trans
      (le_iSup_of_le u le_rfl)

end PlanarNikodym.Family
