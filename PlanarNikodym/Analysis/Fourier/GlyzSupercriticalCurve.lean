import PlanarNikodym.Analysis.Fourier.GlyzSupercriticalMoment
import PlanarNikodym.Analysis.Fourier.GlyzGeneralCurveLocalization

/-! Actual high-p decoupling for finite-regularity nondegenerate curves.
The constants are uniform over the derivative/determinant bounded class. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem glyz_general_curve_critical_decoupling_fin (m : ℕ) (hm : 0 < m)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace m,
      ContDiff ℝ (m + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ m + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ N : ℕ, ∀ f : Fin (2 ^ N) → SchwartzMap (GlyzSpace m) ℂ,
      (∀ i, Function.support (𝓕 (f i : GlyzSpace m → ℂ)) ⊆
        glyzEnlargedCurveBox γ m (glyzDyadicCenter N i) (glyzDyadicScale N) Q) →
      lpNorm ((∑ i, f i : SchwartzMap (GlyzSpace m) ℂ) : GlyzSpace m → ℂ)
          (glyzCriticalNNExponent m) volume ^ 2 ≤ C * (2 : ℝ) ^ (ε * N) *
            ∑ i, lpNorm (f i : GlyzSpace m → ℂ) (glyzCriticalNNExponent m) volume ^ 2 := by
  obtain ⟨C, hC, h⟩ := glyz_general_curve_critical_decoupling m hm hβ hB hQ hε
  refine ⟨C, hC, fun γ hγ hder hdet N f hf => ?_⟩
  have hs : ∀ j < 2 ^ N, Function.support (𝓕 ((glyzFinExtend f j : SchwartzMap (GlyzSpace m) ℂ) : GlyzSpace m → ℂ)) ⊆
      glyzEnlargedCurveBox γ m (glyzDyadicCenter N j) (glyzDyadicScale N) Q := by
    intro j hj
    simpa only [glyzFinExtend, dif_pos hj] using hf ⟨j, hj⟩
  have hh := h γ hγ hder hdet N (glyzFinExtend f) hs
  rw [sum_glyzFinExtend, sum_comp_glyzFinExtend f
    (fun v : SchwartzMap (GlyzSpace m) ℂ =>
      lpNorm (v : GlyzSpace m → ℂ) (glyzCriticalNNExponent m) volume ^ 2)] at hh
  exact hh

theorem glyz_supercritical_curve_power_decoupling (m : ℕ) (hm : 0 < m)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent m ≤ p)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace m,
      ContDiff ℝ (m + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ m + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (f : ℕ → SchwartzMap (GlyzSpace m) ℂ),
      (∀ j < 2 ^ N, Function.support (𝓕 (f j : GlyzSpace m → ℂ)) ⊆
        glyzEnlargedCurveBox γ m (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x, ENNReal.ofReal (‖(∑ i ∈ Finset.range (2 ^ N), f i :
        SchwartzMap (GlyzSpace m) ℂ) x‖ ^ (p : ℝ))) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε) * N)) *
            ∑ i ∈ Finset.range (2 ^ N), ∫⁻ x, ENNReal.ofReal (‖f i x‖ ^ (p : ℝ)) := by
  let q := glyzCriticalNNExponent m
  have hq : 2 ≤ q := two_le_glyzCriticalNNExponent hm
  have hq0 : (0 : ℝ) < q := glyzCriticalExponent_pos hm
  have hqdef : (q : ℝ) = glyzCriticalExponent m := rfl
  have hα : 0 < 2 * ε / (q : ℝ) := by positivity
  by_cases heq : p = q
  · subst p
    obtain ⟨C, hC, hcrit⟩ := glyz_general_curve_critical_decoupling_fin m hm hβ hB hQ hα
    refine ⟨C ^ ((q : ℝ) / 2), Real.rpow_pos_of_pos hC _, fun γ hγ hder hdet N f hf => ?_⟩
    have hh := glyz_fintype_square_to_lp_power
      (fun i : Fin (2 ^ N) => f i) hq
      (show 0 ≤ C * (2 : ℝ) ^ ((2 * ε / (q : ℝ)) * N) by positivity)
      (hcrit γ hγ hder hdet N (fun i : Fin (2 ^ N) => f i) (fun i => hf i i.isLt))
    have hcoef :
        (C * (2 : ℝ) ^ ((2 * ε / (q : ℝ)) * N)) ^ ((q : ℝ) / 2) *
          (Fintype.card (Fin (2 ^ N)) : ℝ) ^ ((q : ℝ) / 2 - 1) =
        C ^ ((q : ℝ) / 2) * (2 : ℝ) ^
          (((q : ℝ) - glyzCriticalExponent m / 2 - 1 + ε) * N) := by
      rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
        glyz_dyadic_power_coefficient hq0 hC.le]
      congr 2
      rw [hqdef]
      ring
    rw [hcoef] at hh
    rw [Fin.sum_univ_eq_sum_range
      (fun i => ∫⁻ x, ENNReal.ofReal (‖f i x‖ ^ (q : ℝ))) (2 ^ N)] at hh
    simpa only [Fin.sum_univ_eq_sum_range] using hh
  · have hpq : (q : ℝ) < p := by
      exact_mod_cast lt_of_le_of_ne hp (Ne.symm heq)
    obtain ⟨M, hM, hinterp⟩ := exists_glyz_affine_boxes_supercritical m hQ
    have hQ' : 0 < glyzBoxCutoffRadius m Q + 1 := by
      unfold glyzBoxCutoffRadius
      positivity
    obtain ⟨C, hC, hcrit⟩ := glyz_general_curve_critical_decoupling_fin m hm hβ hB hQ' hα
    let K := glyzInterpolationFactor p q * C ^ ((q : ℝ) / 2) * M ^ (p : ℝ)
    have hK : 0 < K := mul_pos
      (mul_pos (glyzInterpolationFactor_pos hq0 hpq) (Real.rpow_pos_of_pos hC _))
      (Real.rpow_pos_of_pos hM _)
    refine ⟨K, hK, fun γ hγ hder hdet N f hf => ?_⟩
    obtain ⟨J, _hJ, hframe⟩ := exists_uniform_glyz_general_curve_inverse m hβ hB
    have hframes (i : Fin (2 ^ N)) : ∃ L : GlyzSpace m ≃L[ℝ] GlyzSpace m,
        L.toContinuousLinearMap = glyzCurveJetOperator γ (glyzDyadicCenter N i) := by
      have hiunit := glyzDyadicCenter_mem_Icc i.isLt
      obtain ⟨L, hL, _⟩ := hframe γ (glyzDyadicCenter N i)
        (fun u => hder _ hiunit (u + 1) (by omega)) (hdet _ hiunit)
      exact ⟨L, hL⟩
    choose L hL using hframes
    have hbox (i : Fin (2 ^ N)) (T : ℝ) (hT : 0 ≤ T) :
        glyzEnlargedCurveBox γ m (glyzDyadicCenter N i) (glyzDyadicScale N) T =
        glyzFrequencyBox (glyzScaledFrame (L i) (glyzDyadicScale N) (glyzDyadicScale_pos N))
          (γ (glyzDyadicCenter N i)) T :=
      glyzEnlargedCurveBox_eq_frequencyBox _ _ _ _ (glyzDyadicScale_pos N) hT (L i) (hL i)
    have hh := hinterp (Fin (2 ^ N))
      (fun i => glyzScaledFrame (L i) (glyzDyadicScale N) (glyzDyadicScale_pos N))
      (fun i => γ (glyzDyadicCenter N i)) q hq p
      (C * (2 : ℝ) ^ ((2 * ε / (q : ℝ)) * N)) hpq (by positivity)
      (by intro g hg; exact hcrit γ hγ hder hdet N g (fun i => by
            rw [hbox i _ hQ'.le]; exact hg i))
      (fun i : Fin (2 ^ N) => f i) (fun i => by rw [← hbox i Q hQ.le]; exact hf i i.isLt)
    have hcoef :
        glyzInterpolationFactor p q *
          (C * (2 : ℝ) ^ ((2 * ε / (q : ℝ)) * N)) ^ ((q : ℝ) / 2) *
          (Fintype.card (Fin (2 ^ N)) : ℝ) ^ ((p : ℝ) - (q : ℝ) / 2 - 1) * M ^ (p : ℝ) =
        K * (2 : ℝ) ^ (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε) * N) := by
      rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      calc
        _ = glyzInterpolationFactor p q *
            ((C * (2 : ℝ) ^ ((2 * ε / (q : ℝ)) * N)) ^ ((q : ℝ) / 2) *
              ((2 : ℝ) ^ N) ^ ((p : ℝ) - (q : ℝ) / 2 - 1)) * M ^ (p : ℝ) := by ring
        _ = _ := by
          rw [glyz_dyadic_power_coefficient hq0 hC.le]
          dsimp only [K]
          rw [hqdef]
          ring
    rw [hcoef] at hh
    rw [Fin.sum_univ_eq_sum_range
      (fun i => ∫⁻ x, ENNReal.ofReal (‖f i x‖ ^ (p : ℝ))) (2 ^ N)] at hh
    simpa only [Fin.sum_univ_eq_sum_range] using hh

theorem glyz_supercritical_curve_decoupling (m : ℕ) (hm : 0 < m)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent m ≤ p)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace m,
      ContDiff ℝ (m + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ m + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (f : ℕ → SchwartzMap (GlyzSpace m) ℂ),
      (∀ j < 2 ^ N, Function.support (𝓕 (f j : GlyzSpace m → ℂ)) ⊆
        glyzEnlargedCurveBox γ m (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      lpNorm ((∑ i ∈ Finset.range (2 ^ N), f i : SchwartzMap (GlyzSpace m) ℂ) :
          GlyzSpace m → ℂ) p volume ≤
        C * (2 : ℝ) ^
          ((1 - (glyzCriticalExponent m + 2) / (2 * (p : ℝ)) + ε) * N) *
            (∑ i ∈ Finset.range (2 ^ N),
              lpNorm (f i : GlyzSpace m → ℂ) p volume ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
  have hp0 : 0 < p := lt_of_lt_of_le (show 0 < glyzCriticalNNExponent m from
    glyzCriticalExponent_pos hm) hp
  have hpR : (0 : ℝ) < p := hp0
  obtain ⟨C, hC, h⟩ := glyz_supercritical_curve_power_decoupling m hm hp hβ hB hQ
    (show 0 < ε * (p : ℝ) by positivity)
  refine ⟨C ^ (1 / (p : ℝ)), Real.rpow_pos_of_pos hC _, fun γ hγ hder hdet N f hf => ?_⟩
  have hh := glyz_schwartz_lp_of_power_bound (Finset.range (2 ^ N))
    (∑ i ∈ Finset.range (2 ^ N), f i) f hp0
    (show 0 ≤ C * (2 : ℝ) ^
      (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε * p) * N) by positivity) (h γ hγ hder hdet N f hf)
  have he : (C * (2 : ℝ) ^
      (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε * p) * N)) ^ (1 / (p : ℝ)) =
      C ^ (1 / (p : ℝ)) * (2 : ℝ) ^
        ((1 - (glyzCriticalExponent m + 2) / (2 * (p : ℝ)) + ε) * N) := by
    rw [Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    field_simp
    ring
  rwa [he] at hh


end PlanarNikodym
