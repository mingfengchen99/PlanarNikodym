import PlanarNikodym.Analysis.Fourier.CompactSymbolLpDecay

/-! A pointwise estimate on the actual compact curve graph implies an
Lp estimate for its cutoff average. No global regularity of the input
representative is needed for this domination argument. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem Family.exists_cutoffAverage_Lp_of_graph_bound {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (p : ℝ≥0∞) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (f : Plane → ℂ) (B : ℝ), 0 ≤ B → ∀ X : ℝ≥0∞,
      (∀ x ∈ tsupport χ, ‖f (G.graphMap x.2 x.1)‖ₑ ≤ ENNReal.ofReal B * X) →
      eLpNorm (G.cutoffAverage χ f) p volume ≤ ENNReal.ofReal (A * B) * X := by
  classical
  obtain ⟨x₀, hmax⟩ := hχ.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  let M := ‖χ x₀‖
  let T := Prod.fst '' tsupport χ
  let H := Prod.snd '' tsupport χ
  have hT : IsCompact T := hc.image continuous_fst
  have hH : IsCompact H := hc.image continuous_snd
  let V := (volume T).toReal
  let U := (volume H).toReal ^ (1 / p.toReal)
  refine ⟨V * M * U, by dsimp [V, M, U]; positivity, ?_⟩
  intro f B hB X hb
  have hpoint (q : Parameters 2 d) :
      ‖G.cutoffAverage χ f q‖ₑ ≤ ENNReal.ofReal (V * M * B) * X := by
    calc
      _ ≤ ∫⁻ t, ‖(χ (t, q) : ℂ) * f (G.graphMap q t)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t, T.indicator (fun _ => ENNReal.ofReal M * (ENNReal.ofReal B * X)) t := by
        apply lintegral_mono
        intro t
        by_cases hz : χ (t, q) = 0
        · simp only [hz, Complex.ofReal_zero, zero_mul, enorm_zero, zero_le]
        have hx : (t, q) ∈ tsupport χ := subset_tsupport _ hz
        rw [indicator_of_mem (show t ∈ T from ⟨(t, q), hx, rfl⟩)]
        dsimp only
        rw [enorm_mul]
        apply mul_le_mul
        · rw [← ofReal_norm, Complex.norm_real]
          exact ENNReal.ofReal_le_ofReal (hmax (t, q))
        · exact hb (t, q) hx
        · exact zero_le
        · exact zero_le
      _ = _ := by
        rw [lintegral_indicator_const hT.measurableSet,
          ENNReal.ofReal_mul (by dsimp [V, M]; positivity),
          ENNReal.ofReal_mul (by dsimp [V]; positivity),
          ENNReal.ofReal_toReal hT.measure_ne_top]
        ring
  have hs : ∀ q ∉ H, G.cutoffAverage χ f q = 0 := by
    intro q hq
    apply integral_eq_zero_of_ae
    filter_upwards [] with t
    have hz : χ (t, q) = 0 := image_eq_zero_of_notMem_tsupport
      (fun hx => hq ⟨(t, q), hx, rfl⟩)
    simp [hz]
  have h := eLpNorm_le_finite_support_enorm_bound volume hH.measure_ne_top
    (V * M * B) (by dsimp [V, M]; positivity) X p hpoint hs
  apply h.trans_eq
  congr 2
  dsimp only [U]
  ring

end PlanarNikodym
