import PlanarNikodym.Analysis.Fourier.GlyzOriginalCoarsePower
import PlanarNikodym.Analysis.Fourier.GlyzFiniteGridTransport
import PlanarNikodym.Analysis.Fourier.GlyzShiftedSmoothPartition

/-! Smooth decoupling for the actual cinematic extension operator.
The constant is uniform over every nonnegative partition subordinate
to five fixed shifted grids. Smooth cutoff derivatives never enter it. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace PlanarNikodym

/-- A uniform estimate for every subordinate partition. In particular,
the constant is chosen before the scale and all cutoff functions. -/
theorem Family.exists_glyz_original_colored_coarse_power {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ K)
    (L : ℕ) (hL : 0 < L) (q : ℕ) {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε rmin rmax Q : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      let F := glyzVariableFinalDepth (d + 1) N - q
      ∀ ψ : (Fin 5 × Fin L) → Fin (2 ^ F) → ℝ → ℝ,
      (∀ s j, Continuous (ψ s j)) →
      (∀ s j, tsupport (ψ s j) ⊆ glyzShiftedOpenCell F (glyzSmoothGridShift s.1) j) →
      (∀ s j t, 0 ≤ ψ s j t) →
      (∀ t, ∑ s, ∑ j, ψ s j t ≤ 1) →
      (∀ x t η, a (x, t, η) ≠ 0 → ∑ s, ∑ j, ψ s j t = 1) →
      ∀ r : ℝ, (2 : ℝ) ^ N ≤ r → r ≤ (2 : ℝ) ^ (N + 1) →
      ∀ g : Plane → ℂ, Integrable g →
      Function.support g ⊆ {y | y.2 ∈ Icc rmin rmax} →
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      (∫⁻ x, ‖glyzRawExtension Φ a g r x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * r ^
          (((p : ℝ) - glyzCriticalExponent (d + 1) / 2 - 1) / (d + 1) + ε)) *
          (∑ s, ∑ j, ∫⁻ x,
            ‖glyzRawExtension Φ a (glyzColorInput (ψ s j) g) r x‖ₑ ^ (p : ℝ)) +
        ENNReal.ofReal (C * r ^ (-Q)) * (∫⁻ y, ‖g y‖ₑ) ^ (p : ℝ) := by
  classical
  choose Ks hKs hdetKs hasKs using fun s : (Fin 5 × Fin L) =>
    G.exists_glyzTimeTranslate_regular_support hK hdet has (glyzSmoothGridShift s.1)
  choose Cs hCs hsharp using fun s : (Fin 5 × Fin L) =>
    (G.glyzTimeTranslate (glyzSmoothGridShift s.1)).exists_glyz_original_epsilon_power_coarse
      (G.contDiff_glyzTimeTranslate hG _) (contDiff_glyzTimeTranslateAmplitude ha _)
      (hasCompactSupport_glyzTimeTranslateAmplitude hc _) (hKs s) (hdetKs s) (hasKs s)
      q hp hε hrmin hQ (rmax := rmax)
  let C₀ : ℝ := ∑ s, Cs s
  have hCsC (s : (Fin 5 × Fin L)) : Cs s ≤ C₀ :=
    Finset.single_le_sum (fun i _ => (hCs i).le) (Finset.mem_univ s)
  have hC₀ : 0 < C₀ := (hCs (0, ⟨0, hL⟩)).trans_le (hCsC (0, ⟨0, hL⟩))
  let B : ℝ := (5 * (L : ℝ)) ^ ((p : ℝ) - 1)
  have hB : 0 < B := Real.rpow_pos_of_pos (by positivity) _
  have hp1 : (1 : ℝ) ≤ p :=
    (one_le_glyzCriticalNNExponent (by omega : 0 < d + 1)).trans hp
  refine ⟨B * C₀, mul_pos hB hC₀, fun N ψ hψ hs hnon hsum hone r hr hr' g hg hgr => ?_⟩
  let F := glyzVariableFinalDepth (d + 1) N - q
  let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
  let σ : ℝ := ((p : ℝ) - glyzCriticalExponent (d + 1) / 2 - 1) / (d + 1) + ε
  let w : (Fin 5 × Fin L) → ℝ → ℝ := fun s t => ∑ j, ψ s j t
  have hw (s : (Fin 5 × Fin L)) : Continuous (w s) := continuous_finsetSum _ (fun j _ => hψ s j)
  have hw0 (s : (Fin 5 × Fin L)) (t : ℝ) : 0 ≤ w s t := Finset.sum_nonneg (fun j _ => hnon s j t)
  have hw1 (s : (Fin 5 × Fin L)) (t : ℝ) : w s t ≤ 1 :=
    glyz_color_weight_le_one w hw0 hsum s t
  have hψ1 (s : (Fin 5 × Fin L)) (j : Fin (2 ^ F)) (t : ℝ) : ψ s j t ≤ 1 :=
    (Finset.single_le_sum (fun l _ => hnon s l t) (Finset.mem_univ j)).trans (hw1 s t)
  have hΦ : ContDiff ℝ ∞ Φ := hG.comp (contDiff_snd.prodMk contDiff_fst)
  have hr0 : 0 < r := (pow_pos (by norm_num : (0 : ℝ) < 2) N).trans_le hr
  let E : (Fin 5 × Fin L) → ℝ≥0∞ := fun s => ∑ j : Fin (2 ^ F),
    ∫⁻ x, ‖glyzRawExtension Φ a (glyzColorInput (ψ s j) g) r x‖ₑ ^ (p : ℝ)
  have hcolor (s : (Fin 5 × Fin L)) :
      (∫⁻ x, ‖glyzRawExtension Φ a (glyzColorInput (w s) g) r x‖ₑ ^ (p : ℝ)) ≤
      ENNReal.ofReal (C₀ * r ^ σ) * E s +
      ENNReal.ofReal (C₀ * r ^ (-Q)) * (∫⁻ y, ‖glyzColorInput (w s) g y‖ₑ) ^ (p : ℝ) := by
    let ps : Fin 5 → Fin (2 ^ F) → ℝ → ℝ := fun t j => ψ (t, s.2) j
    let gs := glyzSmoothGridData F ps s.1 g
    have hgs : Integrable gs := integrable_glyzSmoothGridData F ps (fun t j => hψ (t, s.2) j)
      (fun t j x => ⟨hnon (t, s.2) j x, hψ1 (t, s.2) j x⟩) s.1 hg
    have hgsupport := glyzSmoothGridData_support F ps (fun t j => hs (t, s.2) j) s.1 hgr
    have hdec := hsharp s N r hr hr' gs hgs
      (fun _ hy => (hgsupport hy).1) (fun _ hy => (hgsupport hy).2)
    let Φs := fun x : Parameters 2 d × ℝ =>
      (G.glyzTimeTranslate (glyzSmoothGridShift s.1)).γ x.2 x.1
    have hparent : glyzRawExtension Φs (glyzTimeTranslateAmplitude a (glyzSmoothGridShift s.1))
        gs r = glyzRawExtension Φ a (glyzColorInput (w s) g) r := by
      rw [show gs = glyzTimeTranslateInput (glyzColorInput (w s) g)
          (glyzSmoothGridShift s.1) from glyzSmoothGridData_eq_timeTranslate F ps s.1 g]
      exact glyzRawExtension_timeTranslate Φ a (glyzColorInput (w s) g) _ r
    have hchild (j : Fin (2 ^ F)) :
        glyzRawExtension Φs (glyzTimeTranslateAmplitude a (glyzSmoothGridShift s.1))
          (glyzDyadicInput F j gs) r =
        glyzRawExtension Φ a (glyzColorInput (ψ s j) g) r := by
      rw [show glyzDyadicInput F j gs = _ from glyzDyadicInput_smoothGridData F ps (fun t j => hs (t, s.2) j) s.1 g j]
      exact glyzRawExtension_timeTranslate Φ a (glyzColorInput (ψ s j) g) _ r
    change (∫⁻ x, ‖glyzRawExtension Φs (glyzTimeTranslateAmplitude a (glyzSmoothGridShift s.1)) gs r x‖ₑ ^ (p : ℝ)) ≤
      ENNReal.ofReal (Cs s * r ^ σ) *
        (∑ i ∈ Finset.range (2 ^ F), ∫⁻ x,
          ‖glyzRawExtension Φs (glyzTimeTranslateAmplitude a (glyzSmoothGridShift s.1))
            (glyzDyadicInput F i gs) r x‖ₑ ^ (p : ℝ)) +
      ENNReal.ofReal (Cs s * r ^ (-Q)) * (∫⁻ y, ‖gs y‖ₑ) ^ (p : ℝ) at hdec
    rw [hparent, ← Fin.sum_univ_eq_sum_range] at hdec
    simp_rw [hchild] at hdec
    have hmass : (∫⁻ y, ‖gs y‖ₑ) = ∫⁻ y, ‖glyzColorInput (w s) g y‖ₑ := by
      rw [show gs = glyzTimeTranslateInput (glyzColorInput (w s) g)
          (glyzSmoothGridShift s.1) from glyzSmoothGridData_eq_timeTranslate F ps s.1 g]
      exact lintegral_enorm_glyzTimeTranslateInput _ _
    rw [hmass] at hdec
    apply hdec.trans
    apply add_le_add <;> apply mul_le_mul_left <;> apply ENNReal.ofReal_le_ofReal
    · exact mul_le_mul_of_nonneg_right (hCsC s) (Real.rpow_nonneg hr0.le _)
    · exact mul_le_mul_of_nonneg_right (hCsC s) (Real.rpow_nonneg hr0.le _)
  have htotal := glyzRawExtension_color_power_assembly volume hΦ ha hc w hw hw0 hsum hone hg r hp1
    (ENNReal.ofReal (C₀ * r ^ σ)) (ENNReal.ofReal (C₀ * r ^ (-Q))) E hcolor
  have hcard : (Fintype.card (Fin 5 × Fin L) : ℝ≥0∞) ^ ((p : ℝ) - 1) = ENNReal.ofReal B := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_ofNat, B, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast] using
      (ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ 5 * (L : ℝ))
        (sub_nonneg.mpr hp1))
  have hcoef (v : ℝ) : ENNReal.ofReal B * ENNReal.ofReal (C₀ * r ^ v) =
      ENNReal.ofReal ((B * C₀) * r ^ v) := by
    rw [← ENNReal.ofReal_mul hB.le]
    congr 1
    ring
  rw [hcard, mul_add, ← mul_assoc, ← mul_assoc, hcoef, hcoef] at htotal
  exact htotal


/-- An arbitrary finite family embedded injectively in the fixed grid
slots satisfies the estimate with its original individual operators. -/
theorem Family.exists_glyz_original_injected_coarse_power {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ K)
    (L : ℕ) (hL : 0 < L) (q : ℕ) {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε rmin rmax Q : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      let F := glyzVariableFinalDepth (d + 1) N - q
      ∀ (m : ℕ) (χ : Fin m → ℝ → ℝ)
        (slot : Fin m → (Fin 5 × Fin L) × Fin (2 ^ F)),
      Function.Injective slot → (∀ i, Continuous (χ i)) →
      (∀ i, tsupport (χ i) ⊆ glyzShiftedOpenCell F
        (glyzSmoothGridShift (slot i).1.1) (slot i).2) →
      (∀ i t, 0 ≤ χ i t) → (∀ t, ∑ i, χ i t ≤ 1) →
      (∀ x t η, a (x, t, η) ≠ 0 → ∑ i, χ i t = 1) →
      ∀ r : ℝ, (2 : ℝ) ^ N ≤ r → r ≤ (2 : ℝ) ^ (N + 1) →
      ∀ g : Plane → ℂ, Integrable g →
      Function.support g ⊆ {y | y.2 ∈ Icc rmin rmax} →
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      (∫⁻ x, ‖glyzRawExtension Φ a g r x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * r ^
          (((p : ℝ) - glyzCriticalExponent (d + 1) / 2 - 1) / (d + 1) + ε)) *
          (∑ i, ∫⁻ x,
            ‖glyzRawExtension Φ a (glyzColorInput (χ i) g) r x‖ₑ ^ (p : ℝ)) +
        ENNReal.ofReal (C * r ^ (-Q)) * (∫⁻ y, ‖g y‖ₑ) ^ (p : ℝ) := by
  classical
  obtain ⟨C, hC, hmain⟩ := G.exists_glyz_original_colored_coarse_power hG ha hc hK hdet has
    L hL q hp hε hrmin hQ (rmax := rmax)
  refine ⟨C, hC, fun N m χ slot hinj hχ hs hnon hsum hone r hr hr' g hg hgr => ?_⟩
  let F := glyzVariableFinalDepth (d + 1) N - q
  let ψ : (Fin 5 × Fin L) → Fin (2 ^ F) → ℝ → ℝ :=
    fun s j => Function.extend slot χ (fun _ => 0) (s, j)
  have hψsum (t : ℝ) : (∑ s, ∑ j, ψ s j t) = ∑ i, χ i t := by
    have hh := glyz_sum_comp_extend slot hinj χ (fun f => f t) rfl
    rw [Fintype.sum_prod_type] at hh
    exact hh
  have hdec := hmain N ψ
    (fun s j => continuous_glyz_extend_cutoff slot hinj χ hχ (s, j))
    (fun s j => glyz_extend_cutoff_support slot hinj χ
      (fun b => glyzShiftedOpenCell F (glyzSmoothGridShift b.1.1) b.2) hs (s, j))
    (fun s j t => glyz_extend_cutoff_nonneg slot hinj χ hnon (s, j) t)
    (fun t => (hψsum t).le.trans (hsum t))
    (fun x t η hn => (hψsum t).trans (hone x t η hn))
    r hr hr' g hg hgr
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one
    ((one_le_glyzCriticalNNExponent (by omega : 0 < d + 1)).trans hp)
  have he := glyzRawExtension_power_sum_extend volume
    (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a g r hp0 slot hinj χ
  rw [Fintype.sum_prod_type] at he
  dsimp only at hdec ⊢
  simp only [ψ] at hdec
  rw [he] at hdec
  exact hdec

end PlanarNikodym
