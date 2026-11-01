import PlanarNikodym.Analysis.Fourier.GlyzSupercriticalMoment
import PlanarNikodym.Analysis.Fourier.GlyzConeCriticalDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzConeProjector

/-! Actual high-p decoupling for cones over finite-regularity nondegenerate curves.
The constants are uniform over the derivative/determinant bounded class. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem glyz_cone_critical_decoupling_fin (m : ℕ) (hm : 0 < m)
    {β B Q ε rmin rmax : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) (hrmin : 0 < rmin) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace m,
      ContDiff ℝ (m + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ m + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ N : ℕ, ∀ f : Fin (2 ^ N) → SchwartzMap (GlyzConeSpace m) ℂ,
      (∀ i, Function.support (𝓕 (f i : GlyzConeSpace m → ℂ)) ⊆
        glyzConeBox m γ (glyzDyadicCenter N i) (glyzDyadicScale N) Q rmin rmax) →
      lpNorm ((∑ i, f i : SchwartzMap (GlyzConeSpace m) ℂ) : GlyzConeSpace m → ℂ)
          (glyzCriticalNNExponent m) volume ^ 2 ≤ C * (2 : ℝ) ^ (ε * N) *
            ∑ i, lpNorm (f i : GlyzConeSpace m → ℂ) (glyzCriticalNNExponent m) volume ^ 2 := by
  obtain ⟨C, hC, h⟩ := glyz_cone_critical_decoupling m hm hβ hB hQ hε hrmin
  refine ⟨C, hC, fun γ hγ hder hdet N f hf => ?_⟩
  have hs : ∀ j < 2 ^ N, Function.support (𝓕 ((glyzFinExtend f j : SchwartzMap (GlyzConeSpace m) ℂ) : GlyzConeSpace m → ℂ)) ⊆
      glyzConeBox m γ (glyzDyadicCenter N j) (glyzDyadicScale N) Q rmin rmax := by
    intro j hj
    simpa only [glyzFinExtend, dif_pos hj] using hf ⟨j, hj⟩
  have hh := h γ hγ hder hdet N (glyzFinExtend f) hs
  rw [sum_glyzFinExtend, sum_comp_glyzFinExtend f
    (fun v : SchwartzMap (GlyzConeSpace m) ℂ =>
      lpNorm (v : GlyzConeSpace m → ℂ) (glyzCriticalNNExponent m) volume ^ 2)] at hh
  exact hh

theorem glyz_supercritical_cone_power_decoupling (m : ℕ) (hm : 0 < m)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent m ≤ p)
    {β B Q ε rmin rmax : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) (hrmin : 0 < rmin) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace m,
      ContDiff ℝ (m + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ m + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (f : ℕ → SchwartzMap (GlyzConeSpace m) ℂ),
      (∀ j < 2 ^ N, Function.support (𝓕 (f j : GlyzConeSpace m → ℂ)) ⊆
        glyzConeBox m γ (glyzDyadicCenter N j) (glyzDyadicScale N) Q rmin rmax) →
      (∫⁻ x, ENNReal.ofReal (‖(∑ i ∈ Finset.range (2 ^ N), f i :
        SchwartzMap (GlyzConeSpace m) ℂ) x‖ ^ (p : ℝ))) ≤
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
    obtain ⟨C, hC, hcrit⟩ := glyz_cone_critical_decoupling_fin m hm hβ hB hQ hα hrmin
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
    obtain ⟨Q', M, hQ', hM, hcut⟩ := exists_glyz_cone_cutoffs m hQ hrmin (rmax := rmax)
    obtain ⟨C, hC, hcrit⟩ := glyz_cone_critical_decoupling_fin m hm hβ hB hQ' hα
      (show 0 < rmin / 2 by positivity) (rmax := rmax + 1)
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
    have hcutoffs (i : Fin (2 ^ N)) := hcut γ (glyzDyadicCenter N i) (glyzDyadicScale N)
      (glyzDyadicScale_pos N) (L i) (hL i)
    choose χ hχone hχsupp hχmass using hcutoffs
    have hh := glyz_projected_supercritical_decoupling χ hq hpq
      (show 0 ≤ C * (2 : ℝ) ^ ((2 * ε / (q : ℝ)) * N) by positivity) hM hχmass
      (by
        intro g
        rw [glyzProjectionSum_apply]
        exact hcrit γ hγ hder hdet N _ (fun i =>
          (support_fourier_glyzFourierProjector (χ i) (g i)).trans (hχsupp i)))
      (fun i : Fin (2 ^ N) => f i) (fun i z hz => hχone i z (hf i i.isLt hz))
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

theorem glyz_supercritical_cone_decoupling (m : ℕ) (hm : 0 < m)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent m ≤ p)
    {β B Q ε rmin rmax : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) (hrmin : 0 < rmin) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace m,
      ContDiff ℝ (m + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ m + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (f : ℕ → SchwartzMap (GlyzConeSpace m) ℂ),
      (∀ j < 2 ^ N, Function.support (𝓕 (f j : GlyzConeSpace m → ℂ)) ⊆
        glyzConeBox m γ (glyzDyadicCenter N j) (glyzDyadicScale N) Q rmin rmax) →
      lpNorm ((∑ i ∈ Finset.range (2 ^ N), f i : SchwartzMap (GlyzConeSpace m) ℂ) :
          GlyzConeSpace m → ℂ) p volume ≤
        C * (2 : ℝ) ^
          ((1 - (glyzCriticalExponent m + 2) / (2 * (p : ℝ)) + ε) * N) *
            (∑ i ∈ Finset.range (2 ^ N),
              lpNorm (f i : GlyzConeSpace m → ℂ) p volume ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
  have hp0 : 0 < p := lt_of_lt_of_le (show 0 < glyzCriticalNNExponent m from
    glyzCriticalExponent_pos hm) hp
  have hpR : (0 : ℝ) < p := hp0
  obtain ⟨C, hC, h⟩ := glyz_supercritical_cone_power_decoupling m hm hp hβ hB hQ
    (show 0 < ε * (p : ℝ) by positivity) hrmin
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


theorem glyz_supercritical_cone_subset_power_decoupling (m : ℕ) (hm : 0 < m)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent m ≤ p)
    {β B Q ε rmin rmax : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) (hrmin : 0 < rmin) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace m,
      ContDiff ℝ (m + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ m + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (I : Finset ℕ) (f : ℕ → SchwartzMap (GlyzConeSpace m) ℂ),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzConeSpace m → ℂ)) ⊆
        glyzConeBox m γ (glyzDyadicCenter N j) (glyzDyadicScale N) Q rmin rmax) →
      (∫⁻ x, ‖(∑ i ∈ I, f i : SchwartzMap (GlyzConeSpace m) ℂ) x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε) * N)) *
            ∑ i ∈ I, ∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ) := by
  classical
  obtain ⟨C, hC, hglobal⟩ := glyz_supercritical_cone_power_decoupling m hm hp hβ hB hQ hε hrmin
  refine ⟨C, hC, fun γ hγ hder hdet N I f hI hf => ?_⟩
  let g : ℕ → SchwartzMap (GlyzConeSpace m) ℂ := fun j => if j ∈ I then f j else 0
  have hgsupp : ∀ j < 2 ^ N, Function.support (𝓕 (g j : GlyzConeSpace m → ℂ)) ⊆
      glyzConeBox m γ (glyzDyadicCenter N j) (glyzDyadicScale N) Q rmin rmax := by
    intro j _
    by_cases hjI : j ∈ I
    · simpa only [g, if_pos hjI] using hf j hjI
    · simp only [g, if_neg hjI]
      rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_zero]
      simp only [FunLike.coe_zero, Function.support_zero, empty_subset]
  have hsum : (∑ j ∈ Finset.range (2 ^ N), g j) = ∑ j ∈ I, f j := by
    calc
      _ = ∑ j ∈ I, g j := (Finset.sum_subset hI (fun j _ hj => by simp [g, hj])).symm
      _ = _ := Finset.sum_congr rfl fun j hj => by simp only [g, if_pos hj]
  have hp0 : (0 : ℝ) < p := (glyzCriticalExponent_pos hm).trans_le (show _ ≤ (p : ℝ) from hp)
  have henergy : (∑ j ∈ Finset.range (2 ^ N), ∫⁻ x, ‖g j x‖ₑ ^ (p : ℝ)) =
      ∑ j ∈ I, ∫⁻ x, ‖f j x‖ₑ ^ (p : ℝ) := by
    calc
      _ = ∑ j ∈ I, ∫⁻ x, ‖g j x‖ₑ ^ (p : ℝ) :=
        (Finset.sum_subset hI (fun j _ hj => by simp [g, hj, ENNReal.zero_rpow_of_pos hp0])).symm
      _ = _ := Finset.sum_congr rfl fun j hj => by simp only [g, if_pos hj]
  have h := hglobal γ hγ hder hdet N g hgsupp
  simp_rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) p.coe_nonneg, ofReal_norm] at h
  simpa only [hsum, henergy] using h

end PlanarNikodym
