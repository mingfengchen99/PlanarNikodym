import PlanarNikodym.Analysis.Fourier.GlyzOriginalColoredPower
import PlanarNikodym.Analysis.Fourier.GlyzShiftedGridMargin
import PlanarNikodym.Analysis.Fourier.GlyzExactScaleBudget
import PlanarNikodym.Analysis.Fourier.GlyzExactTimePartition

/-! Decoupling of the original cinematic extension into the fixed
standard smooth windows at the literal frequency scale. The coarse
grid and all auxiliary cutoffs disappear from the conclusion. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace PlanarNikodym

theorem glyzExactTimeCount_centers {δ : ℝ} (hδ : 0 < δ)
    (i : Fin (glyzExactTimeCount δ)) :
    (-1 : ℝ) + δ * i ∈ Icc (-1 - δ) (1 + δ) := by
  have hi : (i : ℕ) ≤ ⌈2 / δ⌉₊ := by
    have := i.isLt
    simp only [glyzExactTimeCount] at this
    omega
  have hiR : (i : ℝ) ≤ (⌈2 / δ⌉₊ : ℝ) := by exact_mod_cast hi
  have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 / δ by positivity)
  have hb : (i : ℝ) < 2 / δ + 1 := hiR.trans_lt hc
  have he : (2 / δ : ℝ) * δ = 2 := div_mul_cancel₀ _ hδ.ne'
  have hm := mul_lt_mul_of_pos_right hb hδ
  constructor
  · have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    nlinarith
  · nlinarith

/-- The full original power estimate, with exact smooth time pieces.
The constant is selected before the real frequency and input. -/
theorem Family.exists_glyz_exact_scale_power {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ K)
    (hKt : ∀ x ∈ K, x.1 ∈ Ioo (-1 : ℝ) 1)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε rmin rmax Q : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      ∀ g : Plane → ℂ, Integrable g →
      Function.support g ⊆ {y | y.2 ∈ Icc rmin rmax} →
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      let δ := r ^ (-(1 / (d + 1 : ℝ)))
      (∫⁻ x, ‖glyzRawExtension Φ a g r x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * r ^
          (((p : ℝ) - glyzCriticalExponent (d + 1) / 2 - 1) / (d + 1) + ε)) *
          (∑ i : Fin (glyzExactTimeCount δ), ∫⁻ x,
            ‖glyzRawExtension Φ a (glyzExactTimePiece δ i g) r x‖ₑ ^ (p : ℝ)) +
        ENNReal.ofReal (C * r ^ (-Q)) * (∫⁻ y, ‖g y‖ₑ) ^ (p : ℝ) := by
  classical
  obtain ⟨χ, hχ, _, hχr, hχs, hχ1⟩ := exists_glyz_smooth_time_cutoff
    (hK.image continuous_fst) (by
      rintro t ⟨x, hx, rfl⟩
      exact hKt x hx)
  have hone (x : Parameters 2 d) (t η : ℝ) (hn : a (x, t, η) ≠ 0) : χ t = 1 :=
    hχ1 t ⟨(t, x), has x t η hn, rfl⟩
  obtain ⟨C₀, hC₀, hcoarse⟩ := G.exists_glyz_original_injected_coarse_power
    hG ha hc hK hdet has 4096 (by norm_num) 8 hp hε hrmin hQ (rmax := rmax)
  let B : ℝ := (514 : ℝ) ^ ((p : ℝ) - 1)
  have hB : 0 < B := Real.rpow_pos_of_pos (by norm_num) _
  let C : ℝ := C₀ + B
  have hC : 0 < C := add_pos hC₀ hB
  have hC₀C : C₀ ≤ C := le_add_of_nonneg_right hB.le
  have hBC : B ≤ C := le_add_of_nonneg_left hC₀.le
  have hp1 : (1 : ℝ) ≤ p :=
    (one_le_glyzCriticalNNExponent (by omega : 0 < d + 1)).trans hp
  refine ⟨C, hC, fun r hr g hg hgr => ?_⟩
  let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
  let δ : ℝ := r ^ (-(1 / (d + 1 : ℝ)))
  let β : ℝ := ((p : ℝ) - glyzCriticalExponent (d + 1) / 2 - 1) / (d + 1) + ε
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hδ : 0 < δ := Real.rpow_pos_of_pos hr0 _
  obtain ⟨N, hl, hu⟩ := exists_glyz_frequency_shell hr
  let F := glyzVariableFinalDepth (d + 1) N
  by_cases hF : 8 ≤ F
  · have hb := glyz_exact_frequency_scale_coarse_bounds (by omega : 0 < d + 1) hl hu.le hF
    simp only [Nat.cast_add, Nat.cast_one] at hb
    change 128 * δ ≤ glyzDyadicScale (F - 8) ∧
      glyzDyadicScale (F - 8) ≤ 512 * δ at hb
    obtain ⟨s, l, hs, hinj⟩ := exists_glyz_standard_grid_assignment
      (F - 8) (glyzExactTimeCount δ) hδ (by linarith [hb.1])
      (by linarith [hb.2]) (glyzExactTimeCount_centers hδ)
    let ψ : Fin (glyzExactTimeCount δ) → ℝ → ℝ :=
      fun i t => χ t * scaleTimeCutoff (-1) δ i t
    let slot : Fin (glyzExactTimeCount δ) → (Fin 5 × Fin 4096) × Fin (2 ^ (F - 8)) :=
      fun i => ((s i, ⟨(i : ℕ) % 4096, Nat.mod_lt _ (by norm_num)⟩), l i)
    have hψs (i : Fin (glyzExactTimeCount δ)) : tsupport (ψ i) ⊆
        glyzShiftedOpenCell (F - 8) (glyzSmoothGridShift (slot i).1.1) (slot i).2 := by
      intro t ht
      have htχ : t ∈ tsupport χ := tsupport_mul_subset_left ht
      have htψ : t ∈ tsupport (scaleTimeCutoff (-1) δ i) := tsupport_mul_subset_right ht
      have htI := tsupport_scaleTimeCutoff_subset (-1) hδ i htψ
      have htχI := hχs htχ
      apply hs i
      refine ⟨?_, ⟨htχI.1.le, htχI.2.le⟩⟩
      constructor <;> linarith [htI.1, htI.2]
    have hψsum (t : ℝ) : ∑ i, ψ i t = χ t *
        ∑ i : Fin (glyzExactTimeCount δ), scaleTimeCutoff (-1) δ i t := by
      exact (Finset.mul_sum _ _ _).symm
    have hψsumle (t : ℝ) : ∑ i, ψ i t ≤ 1 := by
      rw [hψsum]
      calc
        χ t * ∑ i : Fin (glyzExactTimeCount δ), scaleTimeCutoff (-1) δ i t ≤ χ t * 1 :=
          mul_le_mul_of_nonneg_left (glyzExactTimePartition_fin_sum_le_one δ t) (hχr t).1
        _ ≤ 1 := by simpa only [mul_one] using (hχr t).2
    have hψone (x : Parameters 2 d) (t η : ℝ) (hn : a (x, t, η) ≠ 0) :
        ∑ i, ψ i t = 1 := by
      rw [hψsum, hone x t η hn,
        glyzExactTimePartition_fin_sum hδ
          ⟨(hKt (t, x) (has x t η hn)).1.le, (hKt (t, x) (has x t η hn)).2.le⟩,
        one_mul]
    have hh := hcoarse N (glyzExactTimeCount δ) ψ slot hinj
      (fun i => hχ.continuous.mul (contDiff_scaleTimeCutoff _ _ _).continuous) hψs
      (fun i t => mul_nonneg (hχr t).1 (scaleTimeCutoff_nonneg _ _ _ _))
      hψsumle hψone r hl hu.le g hg hgr
    dsimp only at hh ⊢
    have he (i : Fin (glyzExactTimeCount δ)) :
        glyzRawExtension Φ a (glyzColorInput (ψ i) g) r =
          glyzRawExtension Φ a (glyzExactTimePiece δ i g) r :=
      glyzRawExtension_exactTimePiece_localize Φ a χ hone g r δ i
    have hea (i : Fin (glyzExactTimeCount δ)) (x : Parameters 2 d) := congrFun (he i) x
    simp only [Φ, ψ] at hea
    simp only [ψ] at hh
    simp_rw [hea] at hh
    apply hh.trans
    apply add_le_add <;> apply mul_le_mul_left <;> apply ENNReal.ofReal_le_ofReal
    · exact mul_le_mul_of_nonneg_right hC₀C (Real.rpow_nonneg hr0.le _)
    · exact mul_le_mul_of_nonneg_right hC₀C (Real.rpow_nonneg hr0.le _)
  · have hlow := glyz_exact_frequency_scale_low_bound (by omega : 0 < d + 1) hl hu.le
      (show glyzVariableFinalDepth (d + 1) N < 8 by omega)
    simp only [Nat.cast_add, Nat.cast_one] at hlow
    have hcount : glyzExactTimeCount δ ≤ 514 := glyzExactTimeCount_low (δ := δ) hlow
    have hΦ : ContDiff ℝ ∞ Φ := hG.comp (contDiff_snd.prodMk contDiff_fst)
    have hh := glyzRawExtension_exactTimePartition_power volume hΦ ha hc
      (fun x t η hn => ⟨(hKt (t, x) (has x t η hn)).1.le,
        (hKt (t, x) (has x t η hn)).2.le⟩) hg r hδ hp1
    have hβ : 0 ≤ β := by
      have hb := glyz_sharp_power_exponent_nonneg (by omega : 0 < d + 1)
        (show glyzCriticalExponent (d + 1) ≤ (p : ℝ) from hp) hε.le
      simpa only [Nat.cast_add, Nat.cast_one] using hb
    have hpow : 1 ≤ r ^ β := Real.one_le_rpow hr hβ
    have hcoef : (glyzExactTimeCount δ : ℝ≥0∞) ^ ((p : ℝ) - 1) ≤
        ENNReal.ofReal (C * r ^ β) := by
      calc
        (glyzExactTimeCount δ : ℝ≥0∞) ^ ((p : ℝ) - 1) ≤
            (514 : ℝ≥0∞) ^ ((p : ℝ) - 1) :=
          ENNReal.rpow_le_rpow (by exact_mod_cast hcount) (sub_nonneg.mpr hp1)
        _ = ENNReal.ofReal B := by
          simpa only [B, ENNReal.ofReal_ofNat] using
            ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 514) (sub_nonneg.mpr hp1)
        _ ≤ ENNReal.ofReal (C * r ^ β) := ENNReal.ofReal_le_ofReal
          (hBC.trans (le_mul_of_one_le_right hC.le hpow))
    exact hh.trans ((mul_le_mul_left hcoef _).trans (le_add_right le_rfl))

end PlanarNikodym
