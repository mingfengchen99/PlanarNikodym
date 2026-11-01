import PlanarNikodym.Analysis.Fourier.UniformNonstationaryPhase
import PlanarNikodym.Analysis.Maximal.E2FIOFullKernel

/-! Uniform nonstationary phase for the actual two-dimensional integral,
obtained by integration by parts in a genuine parameter coordinate and
integration over the remaining compact coordinate. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace PlanarNikodym
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def e2FIOSecondCoordinateDerivative (Φ : P × Plane → ℝ) (z : P × Plane) : ℝ :=
  deriv (fun s : ℝ => Φ (z.1, (z.2.1, s))) z.2.2

theorem e2_exists_uniform_second_coordinate_nonstationary_decay
    {Φ : P × Plane → ℝ} {a : P × Plane → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hne : ∀ z ∈ tsupport a, e2FIOSecondCoordinateDerivative Φ z ≠ 0) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : P) (r : ℝ), r ≠ 0 →
      ‖∫ q : Plane, Complex.exp (((r * Φ (p, q) : ℝ) : ℂ) * Complex.I) * a (p, q)‖ ≤
        C * (|r|⁻¹) ^ N := by
  let e : ((P × ℝ) × ℝ) ≃ₜ (P × Plane) := Homeomorph.prodAssoc P ℝ ℝ
  have heapply (z : (P × ℝ) × ℝ) : e z = (z.1.1, (z.1.2, z.2)) := rfl
  let Ψ := Φ ∘ e
  let b := a ∘ e
  have hΨ : ContDiff ℝ ∞ Ψ :=
    hΦ.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  have hb : ContDiff ℝ ∞ b :=
    ha.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  have hbc : HasCompactSupport b := hc.comp_homeomorph e
  have hbn : ∀ z ∈ tsupport b, partialTimeDeriv Ψ z ≠ 0 := by
    intro z hz
    have hez : e z ∈ tsupport a := by
      exact tsupport_comp_subset_preimage a e.continuous hz
    exact hne (e z) hez
  obtain ⟨B, hB, hdecay⟩ := exists_uniform_nonstationary_decay_constant
    (fun z _ => hΨ.contDiffAt) hb hbc hbn N
  let T : Set ℝ := (fun z : (P × ℝ) × ℝ => z.1.2) '' tsupport b
  have hT : IsCompact T := hbc.isCompact.image (continuous_fst.snd)
  let C : ℝ := B * volume.real T
  refine ⟨C, mul_nonneg hB (by positivity), ?_⟩
  intro p r hr
  let J : Plane → ℂ := fun q => Complex.exp (((r * Φ (p, q) : ℝ) : ℂ) * Complex.I) * a (p, q)
  have hJcont : Continuous J := by
    exact ((Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul
        (hΦ.continuous.comp (continuous_const.prodMk continuous_id)))).mul continuous_const)).mul
      (ha.continuous.comp (continuous_const.prodMk continuous_id)))
  have hJc : HasCompactSupport J := by
    apply HasCompactSupport.intro (hc.isCompact.image continuous_snd)
    intro q hq
    have hz : a (p, q) = 0 := by
      by_contra hn
      exact hq ⟨(p, q), subset_tsupport a hn, rfl⟩
    simp only [J, hz, mul_zero]
  have hJi : Integrable J := hJcont.integrable_of_hasCompactSupport hJc
  have hJiprod : Integrable J ((volume : Measure ℝ).prod volume) := by
    rwa [← Measure.volume_eq_prod]
  have hinner (s : ℝ) : ‖∫ t : ℝ, J (s, t)‖ ≤ T.indicator (fun _ => B * (|r|⁻¹) ^ N) s := by
    by_cases hs : s ∈ T
    · simpa only [indicator_of_mem hs, J, phaseOscillation, Ψ, b, Function.comp_apply, heapply] using
        hdecay (p, s) r hr
    · have hz (t : ℝ) : b ((p, s), t) = 0 := by
        by_contra hn
        exact hs ⟨((p, s), t), subset_tsupport b hn, rfl⟩
      have hh : (∫ t : ℝ, J (s, t)) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [] with t
        change Complex.exp _ * b ((p, s), t) = 0
        rw [hz t, mul_zero]
      simp only [hh, norm_zero, indicator_of_notMem hs, le_refl]
  have hi : Integrable (T.indicator (fun _ => B * (|r|⁻¹) ^ N)) :=
    (integrableOn_const hT.measure_ne_top).integrable_indicator hT.measurableSet
  calc
    _ = ‖∫ s : ℝ, ∫ t : ℝ, J (s, t)‖ := by
      change ‖∫ q : Plane, J q‖ = _
      rw [Measure.volume_eq_prod, integral_prod J hJiprod]
    _ ≤ ∫ s : ℝ, ‖∫ t : ℝ, J (s, t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s : ℝ, T.indicator (fun _ => B * (|r|⁻¹) ^ N) s :=
      integral_mono hJiprod.integral_prod_left.norm hi hinner
    _ = _ := by
      rw [integral_indicator_const _ hT.measurableSet, smul_eq_mul]
      dsimp [C]
      ring

end PlanarNikodym
