import PlanarNikodym.Analysis.Fourier.PartialMainLowLp
import PlanarNikodym.Analysis.Fourier.LocalizedPartialDataMass

/-! Physical localization removes the L¹ error in the genuine high
frequency main estimate. A separate actual kernel bound covers the
bounded remaining frequencies. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace PlanarNikodym
set_option maxHeartbeats 1000000

private theorem partialMain_inverse_power_le_rpow (a : ℝ) {N : ℕ}
    (hN : -a ≤ N) {r : ℝ} (hr : 1 ≤ r) : (r⁻¹) ^ N ≤ r ^ a := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [← Real.rpow_natCast, Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le]
  exact Real.rpow_le_rpow_of_exponent_le hr (by linarith)

private theorem partialMain_low_power_le {r R : ℝ} (hr : 1 ≤ r) (hR : r ≤ R) (a : ℝ) :
    r ^ 2 ≤ R ^ |2 - a| * r ^ a := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have he : r ^ 2 = r ^ (2 - a) * r ^ a := by
    rw [← Real.rpow_add hr0, sub_add_cancel, Real.rpow_ofNat]
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr0.le _)
  exact (Real.rpow_le_rpow_of_exponent_le hr (le_abs_self _)).trans
    (Real.rpow_le_rpow hr0.le hR (abs_nonneg _))

/-- The global scale-uniform main estimate. The only estimate accepted by
this intermediate theorem is the actual high-frequency bound produced by
the decoupling cascade; its L¹ error is removed here by proved kernel tails. -/
theorem Family.exists_partialExtension_global_Lp_of_L1_error {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (a : ℝ)
    (hhigh : ∀ N : ℕ, ∃ R C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, max 1 R ≤ r →
      ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
        eLpNorm (G.cutoffPartialExtension χ L β r f) p volume ≤
          ENNReal.ofReal (C * r ^ a) * eLpNorm f p volume +
          ENNReal.ofReal (C * (r⁻¹) ^ N) * eLpNorm f 1 volume) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ,
      Integrable f → MemLp f p volume →
        eLpNorm (G.cutoffPartialExtension χ L β r f) p volume ≤
          ENNReal.ofReal (C * r ^ a) * eLpNorm f p volume := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge (-a)
  obtain ⟨R₀, hR₀, hfar⟩ := G.exists_partialExtension_physical_localization χ hχ.continuous hc
    (fun x hx => (hγ x hx).continuousAt) L β hβ
  obtain ⟨B, hB, hb⟩ := hfar p hp N
  obtain ⟨R, C, hC, hh⟩ := hhigh N
  obtain ⟨D, hD, hd⟩ := G.exists_partialExtension_polynomial_Lp_bound χ hχ.continuous hc
    (fun x hx => (hγ x hx).continuousAt) L β hβ p hp
  let S : Set Plane := closedBall 0 R₀
  have hSm : MeasurableSet S := measurableSet_closedBall
  have hSv : volume S ≠ (∞ : ℝ≥0∞) := (isCompact_closedBall (0 : Plane) R₀).measure_ne_top
  have hpow : 0 ≤ 1 - 1 / p.toReal := by
    by_cases ht : p = (∞ : ℝ≥0∞)
    · simp [ht]
    · have hpR : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono ht hp
      exact sub_nonneg.mpr (by simpa only [one_div] using inv_le_one_of_one_le₀ hpR)
  let V := ((volume S) ^ (1 - 1 / p.toReal)).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have heV : (volume S) ^ (1 - 1 / p.toReal) = ENNReal.ofReal V := by
    exact (ENNReal.ofReal_toReal (ENNReal.rpow_lt_top_of_nonneg hpow hSv).ne).symm
  let Cbig := C * (1 + V) + B
  let Clow := D * (max 1 R) ^ |2 - a|
  refine ⟨Cbig + Clow, by dsimp [Cbig, Clow]; positivity, ?_⟩
  intro r hr f hf hfp
  have hra : 0 ≤ r ^ a := Real.rpow_nonneg (zero_le_one.trans hr) a
  by_cases hlarge : max 1 R ≤ r
  · let g := S.indicator f
    let h := Sᶜ.indicator f
    have hg : Integrable g := hf.indicator hSm
    have hhi : Integrable h := hf.indicator hSm.compl
    have hgp : MemLp g p volume := hfp.indicator hSm
    have he : f = g + h := by
      funext y
      by_cases hy : y ∈ S <;> simp [g, h, hy]
    have hn : eLpNorm g p volume ≤ eLpNorm f p volume := eLpNorm_indicator_le _
    have hg1 : eLpNorm g 1 volume ≤ eLpNorm f p volume * ENNReal.ofReal V := by
      rw [← heV]
      exact eLpNorm_one_indicator_le_compact_volume hSm hf hp
    have hinv := partialMain_inverse_power_le_rpow a hN hr
    have hnear := hh r hlarge g hg hgp
    have htail := hb r hr f hf
    have hsum := eLpNorm_add_le (μ := (volume : Measure (Parameters 2 d)))
      (G.continuous_partialExtension_of_support χ hχ hc hγ L β hβ.continuous hg r).aestronglyMeasurable
      (G.continuous_partialExtension_of_support χ hχ hc hγ L β hβ.continuous hhi r).aestronglyMeasurable hp
    have hlin := G.cutoffPartialExtension_add χ hχ.continuous hc
      (fun x hx => (hγ x hx).continuousAt) L β hβ.continuous hg hhi r
    calc
      _ ≤ eLpNorm (G.cutoffPartialExtension χ L β r g) p volume +
          eLpNorm (G.cutoffPartialExtension χ L β r h) p volume := by
        rw [he, hlin]
        exact hsum
      _ ≤ (ENNReal.ofReal (C * r ^ a) * eLpNorm f p volume +
            ENNReal.ofReal (C * r ^ a) * (eLpNorm f p volume * ENNReal.ofReal V)) +
          ENNReal.ofReal (B * r ^ a) * eLpNorm f p volume := by
        apply add_le_add
        · exact hnear.trans (add_le_add (mul_le_mul_right hn _)
            (mul_le_mul (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hinv hC))
              hg1 zero_le zero_le))
        · exact htail.trans (mul_le_mul_left
            (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hinv hB)) _)
      _ = ENNReal.ofReal (Cbig * r ^ a) * eLpNorm f p volume := by
        dsimp [Cbig]
        have hexp : (C * (1 + V) + B) * r ^ a =
            C * r ^ a + (C * r ^ a) * V + B * r ^ a := by ring
        rw [hexp, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (mul_nonneg hC hra)]
        ring
      _ ≤ _ := by
        apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ hra
        exact le_add_of_nonneg_right (by dsimp [Clow]; positivity)
  · have hlow := partialMain_low_power_le hr (le_of_not_ge hlarge) a
    calc
      _ ≤ ENNReal.ofReal (D * r ^ 2) * eLpNorm f p volume := hd r hr f hf
      _ ≤ ENNReal.ofReal (Clow * r ^ a) * eLpNorm f p volume := by
        apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        exact (mul_le_mul_of_nonneg_left hlow hD).trans_eq (by dsimp [Clow]; ring)
      _ ≤ _ := by
        apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ hra
        exact le_add_of_nonneg_left (by dsimp [Cbig]; positivity)

end PlanarNikodym
