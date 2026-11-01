import PlanarNikodym.Analysis.Jets.ScalarJetFourier
import PlanarNikodym.Analysis.Maximal.LocalSmoothing
import PlanarNikodym.Analysis.Sobolev.ScaledSobolev

/-! Reduction of the actual operator-valued auxiliary jet to finitely many
scalar weighted averages, with its precise dyadic derivative cost. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators
namespace PlanarNikodym
set_option maxHeartbeats 1000000

theorem Family.auxiliaryJetNorm_le_scalarJet_sum {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (p : ℝ≥0) (hp : 1 ≤ p) (j : ℕ) :
    G.auxiliaryJetNorm χ f p j ≤
      ∑ α : Fin j → Fin d, ∑ b : ScalarJetPath j,
        eLpNorm (G.cutoffAverage
          (G.scalarJetAmplitude χ j (fun i => scalarJetBasis (α i)) b)
          (scalarJetVerticalIter (scalarJetOrder j b) f)) p volume := by
  classical
  let I := (Fin j → Fin d) × ScalarJetPath j
  let F : I → Parameters 2 d → ℂ := fun a => G.cutoffAverage
    (G.scalarJetAmplitude χ j (fun i => scalarJetBasis (a.1 i)) a.2)
    (scalarJetVerticalIter (scalarJetOrder j a.2) f)
  have hF (a : I) : Continuous (F a) :=
    (G.cutoffAverage_contDiff _ (G.contDiff_scalarJetAmplitude χ hχ hγ j _ a.2)
      (G.hasCompactSupport_scalarJetAmplitude χ hc j _ a.2)
      (fun x hx => hγ x (G.tsupport_scalarJetAmplitude_subset χ j _ a.2 hx))
      (contDiff_scalarJetVerticalIter _ hf)).continuous
  have hpoint (q : Parameters 2 d) :
      ‖iteratedFDeriv ℝ j (fun u => G.cutoffAverage χ f (q.1, u)) q.2‖ ≤
        ∑ a : I, ‖F a q‖ := by
    apply (scalarJet_norm_le_sum_coordinates _).trans
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro α _
    rw [G.auxiliary_jet_eq_scalarJet_sum χ hχ hc hγ hf]
    exact norm_sum_le _ _
  unfold auxiliaryJetNorm
  calc
    _ ≤ eLpNorm (fun q => ∑ a : I, ‖F a q‖) p volume := by
      apply eLpNorm_mono_real
      intro q
      simpa only [norm_norm] using hpoint q
    _ ≤ ∑ a : I, eLpNorm (fun q => ‖F a q‖) p volume := by
      have hsum := (eLpNorm_sum_le (s := Finset.univ)
        (μ := (volume : Measure (Parameters 2 d))) (p := (p : ℝ≥0∞))
        (f := fun a : I => fun q : Parameters 2 d => ‖F a q‖)
        (fun a _ => (hF a).norm.aestronglyMeasurable)
        (by exact_mod_cast hp))
      have he : (∑ a : I, fun q : Parameters 2 d => ‖F a q‖) =
          fun q => ∑ a : I, ‖F a q‖ := by
        funext q
        exact Finset.sum_apply q Finset.univ _
      rw [he] at hsum
      exact hsum
    _ = _ := by simp only [eLpNorm_norm, Fintype.sum_prod_type, F, I]

/-- A scalar constant can be pulled through the actual curve integral
without extra assumptions on the input. -/
theorem Family.scalarJet_cutoffAverage_const_mul {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (c : ℂ) (f : Plane → ℂ) :
    G.cutoffAverage χ (fun x => c * f x) = fun q => c * G.cutoffAverage χ f q := by
  funext q
  unfold cutoffAverage
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

/-- Exact size of the frequency factor left by the vertical derivative. -/
theorem scalarJet_fourierFactor_enorm (m k : ℕ) :
    ‖((((2 * Real.pi * (2 : ℝ) ^ k : ℝ) : ℂ) * Complex.I) ^ m)‖ₑ =
      ENNReal.ofReal ((2 * Real.pi) ^ m) * dyadicWeight (m : ℝ) k := by
  rw [← ofReal_norm, norm_pow, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow,
    ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi) ^ m)]
  congr 1
  simp only [dyadicWeight, Real.rpow_natCast,
    ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 ^ m)]
  rw [pow_right_comm]

/-- The differentiated band is estimated using the original input and a
fixed normalized frequency weight. -/
theorem Family.eLpNorm_scalarJetVerticalIter_band {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (L : FrequencyCutoff) {f : Plane → ℂ} (hf : Integrable f)
    (p : ℝ≥0) (m k : ℕ) :
    eLpNorm (G.cutoffAverage χ (scalarJetVerticalIter m (L.band k f))) p volume =
      ENNReal.ofReal ((2 * Real.pi) ^ m) * dyadicWeight (m : ℝ) k *
        eLpNorm (G.cutoffAverage χ (scaledFrequencyConvolution
          (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ) ((2 : ℝ) ^ k) f)) p volume := by
  rw [L.scalarJetVerticalIter_band hf m k, G.scalarJet_cutoffAverage_const_mul]
  change eLpNorm ((_ : ℂ) • G.cutoffAverage χ _) p volume = _
  rw [eLpNorm_const_smul, scalarJet_fourierFactor_enorm, mul_assoc]

end PlanarNikodym
