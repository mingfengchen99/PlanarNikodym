import PlanarNikodym.Analysis.Fourier.GlyzConeSpectralDecoupling
import PlanarNikodym.Analysis.Fourier.OscillatoryConeSpectralApproximation

/-! A genuine local decoupling inequality for compact oscillatory
extension kernels. The spectral tail is evaluated by the proved
uniform symbol estimates, including unrestricted Taylor oscillation. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

def glyzCurveConeFrequency (k : ℕ) (γ : ℝ → GlyzSpace k) (ρ : ℝ) (y : Plane) :
    GlyzConeSpace k := ρ • WithLp.toLp 2 (y.2 • γ y.1, y.2)

theorem contDiff_glyzCurveConeFrequency (k : ℕ) {γ : ℝ → GlyzSpace k}
    (hγ : ContDiff ℝ ∞ γ) (ρ : ℝ) : ContDiff ℝ ∞ (glyzCurveConeFrequency k γ ρ) := by
  apply ContDiff.const_smul
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (GlyzSpace k) ℝ).symm.contDiff.comp
    ((contDiff_snd.smul (hγ.comp contDiff_fst)).prodMk contDiff_snd)

/-- The constants are uniform over the entire actual symbol family;
its derivative bounds are estimates of explicit functions, not an
assumed decoupling inequality. -/
theorem glyz_oscillatory_cone_local_lp {P : Type*} (k A M : ℕ) (hk : 0 < k)
    (a : P → GlyzConeSpace k × Plane → ℂ) (H : P → GlyzConeSpace k × Plane → ℝ)
    (ha : ∀ u, ContDiff ℝ ∞ (a u)) (hH : ∀ u, ContDiff ℝ ∞ (H u))
    (hc : ∀ u, HasCompactSupport (a u))
    {K : Set (GlyzConeSpace k)} (hK : IsCompact K)
    (hs : ∀ u y, tsupport (fun x => a u (x, y)) ⊆ K)
    (haj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ u y x,
      ‖iteratedFDeriv ℝ n (fun z => a u (z, y)) x‖ ≤ B)
    (hHj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ u y x,
      ‖iteratedFDeriv ℝ n (fun z => H u (z, y)) x‖ ≤ B)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent k ≤ p)
    {β B ε rmin rmax : ℝ} (hβ : 0 < β) (hB : 0 < B)
    (hε : 0 < ε) (hrmin : 0 < rmin) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ γ : ℝ → GlyzSpace k,
      ContDiff ℝ ∞ γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ k + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (u : P) (α : ℝ) (N : ℕ) (ρ T : ℝ), 0 < ρ → 0 < T →
      1 + 2 * ((1 + |α|) * T) ≤ (rmin / 4) * ρ * glyzDyadicScale N ^ k →
      ∀ (I : Finset ℕ) (J : ℕ → Set ℝ) (g : ℕ → Plane → ℂ),
      I ⊆ Finset.range (2 ^ N) → (∀ i, IsCompact (J i)) →
      (∀ i ∈ I, J i ⊆ Icc (0 : ℝ) 1) →
      (∀ i ∈ I, ∀ t ∈ J i, |t - glyzDyadicCenter N i| ≤ glyzDyadicScale N) →
      (∀ i, Integrable (g i)) → (∀ i ∈ I, Function.support (g i) ⊆ J i ×ˢ Icc rmin rmax) →
      let E := fun i => oscillatoryConeExtension (a u) (H u) α (glyzCurveConeFrequency k γ ρ) (g i)
      let e := fun i => (D * (1 + |α|) ^ (volume : Measure (GlyzConeSpace k)).integrablePower *
        (T⁻¹) ^ M) * ∫ y, ‖g i y‖
      let W := fun x : GlyzConeSpace k => ENNReal.ofReal (glyzNormWeight A x)
      (∫⁻ x in closedBall (0 : GlyzConeSpace k) 1, ‖∑ i ∈ I, E i x‖ₑ ^ (p : ℝ)) ≤
        (2 : ℝ≥0∞) ^ (p : ℝ) *
          (ENNReal.ofReal (C * (2 : ℝ) ^
            (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N)) *
              ((2 : ℝ≥0∞) ^ (p : ℝ) *
                ((∑ i ∈ I, ∫⁻ x, ‖E i x‖ₑ ^ (p : ℝ) * W x) +
                  (∑ i ∈ I, ENNReal.ofReal (e i) ^ (p : ℝ)) * ∫⁻ x, W x)) +
            ENNReal.ofReal (∑ i ∈ I, e i) ^ (p : ℝ) *
              volume (closedBall (0 : GlyzConeSpace k) 1)) := by
  obtain ⟨C, hC, hcone⟩ := glyz_cone_spectral_local_lp k A hk hp hβ hB hε hrmin (rmax := rmax)
  obtain ⟨D, hD, htail⟩ := exists_uniform_oscillatoryConeExtension_fourier_tail
    a H ha hH hc hK hs haj hHj M
  refine ⟨C, D, hC, hD, fun γ hγ hder hdet u α N ρ T hρ hT hscale I J g hI hJ hJu hJc hg hgs => ?_⟩
  let ν := glyzCurveConeFrequency k γ ρ
  have hν : ContDiff ℝ ∞ ν := contDiff_glyzCurveConeFrequency k hγ ρ
  let G : ℕ → SchwartzMap (GlyzConeSpace k) ℂ := fun i =>
    oscillatoryConeExtensionSchwartz (a u) (H u) (ha u) (hH u) (hc u) α ν hν (g i) (hg i)
  have hb (i : ℕ) (hi : i ∈ I) :
      glyzConeSpectralTail k γ (J i) rmin rmax ρ ((1 + |α|) * T) (G i) ≤
        (D * (1 + |α|) ^ (volume : Measure (GlyzConeSpace k)).integrablePower *
          (T⁻¹) ^ M) * ∫ y, ‖g i y‖ := by
    apply htail u α ν hν (g i) (hg i)
      ((fun v : GlyzConeSpace k => ρ • v) '' glyzConeArc k γ (J i) rmin rmax) ?_ T hT
    intro y hy
    exact ⟨WithLp.toLp 2 (y.2 • γ y.1, y.2), ⟨y, hgs i hi hy, rfl⟩, rfl⟩
  have h := hcone γ (hγ.of_le (by exact_mod_cast (le_top : ((k + 1 : ℕ) : ℕ∞) ≤ ⊤))) hder hdet N ρ ((1 + |α|) * T)
    hρ (by positivity) hscale I J G hI hJ hJu hJc
  simp only [sum_apply, G, oscillatoryConeExtensionSchwartz_apply] at h
  apply h.trans
  dsimp only
  gcongr with i hi
  · exact hb i hi
  · exact hb _ (by assumption)

end PlanarNikodym
