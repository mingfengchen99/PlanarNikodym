import PlanarNikodym.Analysis.Fourier.E3SmoothLinearL2
import PlanarNikodym.Analysis.Fourier.E3SmoothInverseChartAmplitude

/-! A uniform original time-slice L² estimate for C∞ cinematic phases
and C∞ inverse charts. The actual compact amplitudes and Fourier
constant are constructed before the frequency, time center and input. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

theorem Family.exists_e3_uniform_linear_chart_slice_sq_bound
    {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (E : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2))
    (hi : ∀ x ∈ E.target, ContDiffAt ℝ ∞ E.symm x) (σ : Fin 2 ↪ Fin (d + 2))
    (a : Parameters 2 d × ℝ × ℝ → ℂ) (ha : ContDiff ℝ ∞ a)
    {T : Set ((ℝ × Aux (d + 2)) × Aux 2)} (hT : IsCompact T) (hTE : T ⊆ E.target)
    {J : Set ℝ} (hJ : IsCompact J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (v : Aux (d + 2))
      (e : OpenPartialHomeomorph (Aux 2) (Aux 2)) (hm : 2 ≤ d + 2),
      (∀ z, e z = G.lowerCinematicJetMap hm σ c v z) →
      (∀ x ∈ e.source, ContDiffAt ℝ ∞ e x) →
      ∀ (K : Set (Aux 2)), MeasurableSet K → K ⊆ e.source →
      ∀ β : ℝ, 0 ≤ β →
      (∀ z ∈ K, β ≤ |LinearMap.det (fderiv ℝ e z).toLinearMap|) →
      (∀ y ∈ e '' K, ((c, v), y) ∈ T) →
      (∀ y ∈ e '' K, (E.symm ((c, v), y)).2 = e.symm y) →
      ∀ (h : Plane → ℂ), Measurable h → Integrable h → MemLp h 2 volume →
      ∀ κ r δ : ℝ, 0 < κ → 0 < r → 0 < δ → δ ≤ 1 →
      (2 * Real.pi * r) * δ ^ (2 : ℕ) ∈ Icc (0 : ℝ) 1 →
      (∀ x : Plane, |x.2| < κ → h x = 0) →
      (∀ x : Plane, x.2 ∉ J → h x = 0) →
      ENNReal.ofReal β * (∫⁻ z in K,
        ‖timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h
          (2 * Real.pi * r) c δ (parameterFrame d (v + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ)) ≤
        ENNReal.ofReal (C ^ (2 : ℕ) * κ⁻¹ * r⁻¹ ^ (2 : ℕ)) *
          ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ) := by
  have hΦ : ContDiff ℝ ∞ (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) :=
    hG.comp (contDiff_snd.prodMk contDiff_fst)
  obtain ⟨S, C, hC, hmatch, _, hcoef, _⟩ :=
    exists_e3_uniform_inverseChart_amplitude_cone_bound E hi σ ha hΦ hT hTE hJ
  refine ⟨C, hC, ?_⟩
  intro c v e hm he hea K hK hKS β hβ hJac himage hinverse
    h hh h1 h2 κ r δ hκ hr hδ hδ1 hα hgap hη
  let b := S ((c, v), ((2 * Real.pi * r) * δ ^ (2 : ℕ), δ))
  have hb (y : Aux 2) (hy : y ∈ e '' K) (τ η : ℝ)
      (hhx : h (c + δ * τ, η) ≠ 0) :
      b ((y 0, y 1), (τ, η)) =
        actualTaylorAmplitude a (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
          1 (2 * Real.pi * r) c δ
          (parameterFrame d (v + coordinateInsertion σ (e.symm y))) τ η := by
    have hηJ : η ∈ J := by
      by_contra hn
      exact hhx (hη (c + δ * τ, η) hn)
    have ht := uniformInverseChart_amplitude_eq_actual E σ a hΦ S hmatch
      (himage y hy) (2 * Real.pi * r) δ τ hηJ hα ⟨hδ.le, hδ1⟩
    dsimp only at ht
    rw [hinverse y hy] at ht
    exact ht
  have hbound := G.e3_lintegral_timeSliceExtension_unscaled_linear_chart_sq_le
    hm σ v c e he hea hG hK hKS hβ hJac a h hh h1 h2 hκ hr hδ hgap b hb
  calc
    _ ≤ (∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier b ζ‖ₑ) ^ (2 : ℕ) *
        (ENNReal.ofReal (κ⁻¹ * r⁻¹ ^ (2 : ℕ)) * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ)) := hbound
    _ ≤ (ENNReal.ofReal C) ^ (2 : ℕ) *
        (ENNReal.ofReal (κ⁻¹ * r⁻¹ ^ (2 : ℕ)) * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ)) := by
      gcongr
      exact hcoef _
    _ = _ := by
      rw [← ENNReal.ofReal_pow hC, ← mul_assoc,
        ← ENNReal.ofReal_mul (sq_nonneg C)]
      congr 2
      ring

end PlanarNikodym
