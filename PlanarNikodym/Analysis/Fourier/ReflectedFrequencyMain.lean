import PlanarNikodym.Analysis.Fourier.PartialExtensionLInfinity

/-! Negative vertical frequencies reduce to positive ones by conjugating
the input and reflecting the real frequency cutoff. The curve phase,
physical coordinates, and all input Lp norms are preserved. -/
noncomputable section
open Set MeasureTheory Complex
open scoped ContDiff ENNReal ComplexConjugate
namespace PlanarNikodym

def FrequencyCutoff.centralReflect (L : FrequencyCutoff) : FrequencyCutoff where
  symbol := fun ξ => L.symbol (-ξ)
  smooth := L.smooth.comp contDiff_neg
  compact := L.compact.comp_homeomorph (Homeomorph.neg Plane)
  near_zero := fun ξ hξ => L.near_zero (-ξ) (by simpa only [norm_neg] using hξ)

@[simp] theorem FrequencyCutoff.bandSymbol_centralReflect (L : FrequencyCutoff)
    (k : ℕ) (ξ : Plane) :
    L.centralReflect.bandSymbol k ξ = L.bandSymbol k (-ξ) := by
  simp only [bandSymbol, lowSymbol, centralReflect, smul_neg]

theorem planeFourierCharacter_conjugate (x ξ : Plane) :
    conj (planeFourierCharacter x ξ) = planeFourierCharacter x (-ξ) := by
  unfold planeFourierCharacter
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, fourierPhase,
    Prod.fst_neg, Prod.snd_neg]
  push_cast
  ring

theorem inverseFourierIntegral_reflect (m : Plane → ℝ) (x : Plane) :
    inverseFourierIntegral (fun ξ => m (-ξ)) x = conj (inverseFourierIntegral m x) := by
  change (∫ ξ : Plane, (m (-ξ) : ℂ) * planeFourierCharacter x ξ) =
    conj (∫ ξ : Plane, (m ξ : ℂ) * planeFourierCharacter x ξ)
  rw [← integral_conj]
  simp_rw [map_mul, Complex.conj_ofReal, planeFourierCharacter_conjugate]
  have h := integral_neg_eq_self
    (fun ξ : Plane => (m (-ξ) : ℂ) * planeFourierCharacter x ξ) (volume : Measure Plane)
  simpa only [neg_neg] using h.symm

theorem scaledFrequencyConvolution_reflect (m : Plane → ℝ) (r : ℝ)
    (f : Plane → ℂ) (x : Plane) :
    scaledFrequencyConvolution (fun ξ => m (-ξ)) r (fun y => conj (f y)) x =
      conj (scaledFrequencyConvolution m r f x) := by
  unfold scaledFrequencyConvolution
  simp_rw [inverseFourierIntegral_reflect, ← map_mul]
  rw [integral_conj]
  exact (Complex.conjCLE.map_smul (r ^ 2) _).symm

theorem Family.cutoffAverage_conjugate {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (f : Plane → ℂ) (q : Parameters 2 d) :
    G.cutoffAverage χ (fun y => conj (f y)) q = conj (G.cutoffAverage χ f q) := by
  unfold cutoffAverage
  rw [← integral_conj]
  simp only [map_mul, Complex.conj_ofReal]

theorem integrable_complex_conjugate {f : Plane → ℂ} (hf : Integrable f) :
    Integrable (fun x => conj (f x)) :=
  Complex.conjCLE.toContinuousLinearMap.integrable_comp hf

theorem eLpNorm_complex_conjugate {α : Type*} [MeasureSpace α]
    (f : α → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun x => conj (f x)) p volume = eLpNorm f p volume :=
  eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => norm_conj (f x))

theorem memLp_complex_conjugate {f : Plane → ℂ} {p : ℝ≥0∞} (hf : MemLp f p volume) :
    MemLp (fun x => conj (f x)) p volume :=
  ⟨Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable,
    (eLpNorm_complex_conjugate f p).trans_lt hf.eLpNorm_lt_top⟩

theorem Family.cutoffPartialExtension_reflect {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) (q : Parameters 2 d) :
    G.cutoffPartialExtension χ L.centralReflect (fun η => β (-η)) r
      (fun x => conj (f x)) q = conj (G.cutoffPartialExtension χ L β r f q) := by
  rw [G.cutoffPartialExtension_eq_scaledFrequencyConvolution χ hχ hc hγ
    L.centralReflect (fun η => β (-η)) (hβ.comp continuous_neg)
    (integrable_complex_conjugate hf) r q]
  have hm : (fun ξ : Plane => L.centralReflect.bandSymbol 0 ξ * β (-ξ.2)) =
      fun ξ : Plane => (fun y : Plane => L.bandSymbol 0 y * β y.2) (-ξ) := by
    funext ξ
    simp only [FrequencyCutoff.bandSymbol_centralReflect, Prod.snd_neg]
  rw [hm]
  have he : scaledFrequencyConvolution
      (fun ξ : Plane => (fun y : Plane => L.bandSymbol 0 y * β y.2) (-ξ)) r
      (fun x => conj (f x)) = fun x => conj
        (scaledFrequencyConvolution (fun y : Plane => L.bandSymbol 0 y * β y.2) r f x) := by
    funext x
    exact scaledFrequencyConvolution_reflect (fun y : Plane => L.bandSymbol 0 y * β y.2) r f x
  rw [he]
  rw [G.cutoffAverage_conjugate,
    G.cutoffPartialExtension_eq_scaledFrequencyConvolution χ hχ hc hγ L β hβ hf r q]

end PlanarNikodym
