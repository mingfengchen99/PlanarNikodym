import PlanarNikodym.Analysis.Fourier.FourierKernels
import PlanarNikodym.Analysis.Maximal.MaximalAssembly

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

/-- Every exponent at least one has an extended nonnegative Hölder conjugate,
including the endpoint pair `1, ∞`. -/
theorem exists_ennreal_holder_conjugate (p : ℝ≥0∞) (hp : 1 ≤ p) :
    ∃ q : ℝ≥0∞, ENNReal.HolderConjugate q p := by
  refine ⟨(1 - p⁻¹)⁻¹, ?_⟩
  apply ENNReal.holderConjugate_iff.mpr
  rw [inv_inv]
  exact tsub_add_cancel_of_le (by simpa using ENNReal.inv_le_inv.mpr hp)

/-- A compact cutoff and a Schwartz low-frequency kernel give the full
low-frequency maximal estimate. The estimate uses a uniform convolution
bound and the finite measure of the cutoff's centre projection. -/
theorem lowFrequencyInput_of_compactCutoff {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (L : FrequencyCutoff) (p : ℝ≥0)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (hp : 1 ≤ p) :
    LowFrequencyInput G χ L p := by
  classical
  obtain ⟨q, hq⟩ := exists_ennreal_holder_conjugate (p : ℝ≥0∞) (by exact_mod_cast hp)
  letI : ENNReal.HolderConjugate q (p : ℝ≥0∞) := hq
  obtain ⟨x₀, hx₀⟩ := hχ.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  let M : ℝ := ‖χ x₀‖
  let T : Set ℝ := Prod.fst '' tsupport χ
  let S : Set (Base 2) := (fun x : ℝ × Parameters 2 d => x.2.1) '' tsupport χ
  have hT : IsCompact T := hc.image continuous_fst
  have hS : IsCompact S := hc.image (continuous_fst.comp continuous_snd)
  let A : ℝ≥0∞ := volume T * ENNReal.ofReal M * eLpNorm L.lowKernel q volume
  let C : ℝ≥0∞ := A * volume S ^ (1 / (p : ℝ))
  have hA : A ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hT.measure_lt_top.ne ENNReal.ofReal_ne_top)
      (L.lowKernel_memLp q).eLpNorm_ne_top
  have hC : C ≠ ⊤ := by
    exact ENNReal.mul_ne_top hA (ENNReal.rpow_ne_top_of_nonneg (by positivity) hS.measure_lt_top.ne)
  refine ⟨C.toNNReal, ?_⟩
  intro f _ hf
  let F : ℝ≥0∞ := eLpNorm f p volume
  have havg (z : Base 2) (u : Aux d) :
      ‖G.cutoffAverage χ (L.low f) (z, u)‖ₑ ≤ A * F := by
    calc
      _ ≤ ∫⁻ t, ‖(χ (t, (z, u)) : ℂ) * L.low f (G.graphMap (z, u) t)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t, T.indicator
          (fun _ => ENNReal.ofReal M * eLpNorm L.lowKernel q volume * F) t := by
        apply lintegral_mono
        intro t
        by_cases ht : t ∈ T
        · rw [indicator_of_mem ht]
          dsimp only
          rw [enorm_mul, mul_assoc]
          apply mul_le_mul
          · rw [← ofReal_norm, Complex.norm_real]
            exact ENNReal.ofReal_le_ofReal (hx₀ (t, (z, u)))
          · exact L.low_enorm_le hf.aestronglyMeasurable _
          · exact zero_le
          · exact zero_le
        · rw [indicator_of_notMem ht]
          have hz : χ (t, (z, u)) = 0 := image_eq_zero_of_notMem_tsupport
            (fun h => ht ⟨(t, (z, u)), h, rfl⟩)
          simp only [hz, Complex.ofReal_zero, zero_mul, enorm_zero, le_refl]
      _ = A * F := by
        rw [lintegral_indicator_const hT.measurableSet]
        dsimp [A]
        ring
  have hmax (z : Base 2) :
      G.cutoffMaximal χ (L.low f) z ≤ S.indicator (fun _ => A * F) z := by
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz]
      exact iSup_le (havg z)
    · rw [indicator_of_notMem hz]
      apply iSup_le
      intro u
      have hzero : G.cutoffAverage χ (L.low f) (z, u) = 0 := by
        unfold Family.cutoffAverage
        apply integral_eq_zero_of_ae
        filter_upwards [] with t
        have ht : χ (t, (z, u)) = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hz ⟨(t, (z, u)), h, rfl⟩)
        simp [ht]
      simp only [hzero, enorm_zero, le_refl]
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hp))
  calc
    _ ≤ eLpNorm (S.indicator (fun _ => A * F)) p volume :=
      eLpNorm_mono_enorm (fun z => by simpa only [enorm_eq_self] using hmax z)
    _ = (A * F) * volume S ^ (1 / (p : ℝ)) := by
      rw [eLpNorm_indicator_const hS.measurableSet hp0 ENNReal.coe_ne_top]
      simp only [enorm_eq_self, ENNReal.coe_toReal]
    _ = C * F := by dsimp [C]; ring
    _ = _ := by rw [ENNReal.coe_toNNReal hC]

end PlanarNikodym
