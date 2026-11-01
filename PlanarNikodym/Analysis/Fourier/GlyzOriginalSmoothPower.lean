import PlanarNikodym.Analysis.Fourier.GlyzOriginalRefinedPower
import PlanarNikodym.Analysis.Fourier.GlyzSmoothColorAssembly
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
theorem Family.exists_glyz_original_smooth_power_uniform {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ K)
    (q : ℕ) {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε rmin rmax Q : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      let F := glyzVariableFinalDepth (d + 1) N + q
      ∀ ψ : Fin 5 → Fin (2 ^ F) → ℝ → ℝ,
      (∀ s j, Continuous (ψ s j)) →
      (∀ s j, tsupport (ψ s j) ⊆ glyzShiftedOpenCell F (glyzSmoothGridShift s) j) →
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
  choose Ks hKs hdetKs hasKs using fun s : Fin 5 =>
    G.exists_glyzTimeTranslate_regular_support hK hdet has (glyzSmoothGridShift s)
  choose Cs hCs hsharp using fun s : Fin 5 =>
    (G.glyzTimeTranslate (glyzSmoothGridShift s)).exists_glyz_original_epsilon_power_refined
      (G.contDiff_glyzTimeTranslate hG _) (contDiff_glyzTimeTranslateAmplitude ha _)
      (hasCompactSupport_glyzTimeTranslateAmplitude hc _) (hKs s) (hdetKs s) (hasKs s)
      q hp hε hrmin hQ (rmax := rmax)
  let C₀ : ℝ := ∑ s, Cs s
  have hCsC (s : Fin 5) : Cs s ≤ C₀ :=
    Finset.single_le_sum (fun i _ => (hCs i).le) (Finset.mem_univ s)
  have hC₀ : 0 < C₀ := (hCs 0).trans_le (hCsC 0)
  let B : ℝ := (5 : ℝ) ^ ((p : ℝ) - 1)
  have hB : 0 < B := Real.rpow_pos_of_pos (by norm_num) _
  have hp1 : (1 : ℝ) ≤ p :=
    (one_le_glyzCriticalNNExponent (by omega : 0 < d + 1)).trans hp
  refine ⟨B * C₀, mul_pos hB hC₀, fun N ψ hψ hs hnon hsum hone r hr hr' g hg hgr => ?_⟩
  let F := glyzVariableFinalDepth (d + 1) N + q
  let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
  let σ : ℝ := ((p : ℝ) - glyzCriticalExponent (d + 1) / 2 - 1) / (d + 1) + ε
  let w : Fin 5 → ℝ → ℝ := fun s t => ∑ j, ψ s j t
  have hw (s : Fin 5) : Continuous (w s) := continuous_finsetSum _ (fun j _ => hψ s j)
  have hw0 (s : Fin 5) (t : ℝ) : 0 ≤ w s t := Finset.sum_nonneg (fun j _ => hnon s j t)
  have hw1 (s : Fin 5) (t : ℝ) : w s t ≤ 1 :=
    glyz_color_weight_le_one w hw0 hsum s t
  have hψ1 (s : Fin 5) (j : Fin (2 ^ F)) (t : ℝ) : ψ s j t ≤ 1 :=
    (Finset.single_le_sum (fun l _ => hnon s l t) (Finset.mem_univ j)).trans (hw1 s t)
  have hΦ : ContDiff ℝ ∞ Φ := hG.comp (contDiff_snd.prodMk contDiff_fst)
  have hr0 : 0 < r := (pow_pos (by norm_num : (0 : ℝ) < 2) N).trans_le hr
  let E : Fin 5 → ℝ≥0∞ := fun s => ∑ j : Fin (2 ^ F),
    ∫⁻ x, ‖glyzRawExtension Φ a (glyzColorInput (ψ s j) g) r x‖ₑ ^ (p : ℝ)
  have hcolor (s : Fin 5) :
      (∫⁻ x, ‖glyzRawExtension Φ a (glyzColorInput (w s) g) r x‖ₑ ^ (p : ℝ)) ≤
      ENNReal.ofReal (C₀ * r ^ σ) * E s +
      ENNReal.ofReal (C₀ * r ^ (-Q)) * (∫⁻ y, ‖glyzColorInput (w s) g y‖ₑ) ^ (p : ℝ) := by
    let gs := glyzSmoothGridData F ψ s g
    have hgs : Integrable gs := integrable_glyzSmoothGridData F ψ hψ
      (fun s j t => ⟨hnon s j t, hψ1 s j t⟩) s hg
    have hgsupport := glyzSmoothGridData_support F ψ hs s hgr
    have hdec := hsharp s N r hr hr' gs hgs
      (fun _ hy => (hgsupport hy).1) (fun _ hy => (hgsupport hy).2)
    let Φs := fun x : Parameters 2 d × ℝ =>
      (G.glyzTimeTranslate (glyzSmoothGridShift s)).γ x.2 x.1
    have hparent : glyzRawExtension Φs (glyzTimeTranslateAmplitude a (glyzSmoothGridShift s))
        gs r = glyzRawExtension Φ a (glyzColorInput (w s) g) r := by
      rw [show gs = glyzTimeTranslateInput (glyzColorInput (w s) g)
          (glyzSmoothGridShift s) from glyzSmoothGridData_eq_timeTranslate F ψ s g]
      exact glyzRawExtension_timeTranslate Φ a (glyzColorInput (w s) g) _ r
    have hchild (j : Fin (2 ^ F)) :
        glyzRawExtension Φs (glyzTimeTranslateAmplitude a (glyzSmoothGridShift s))
          (glyzDyadicInput F j gs) r =
        glyzRawExtension Φ a (glyzColorInput (ψ s j) g) r := by
      rw [show glyzDyadicInput F j gs = _ from glyzDyadicInput_smoothGridData F ψ hs s g j]
      exact glyzRawExtension_timeTranslate Φ a (glyzColorInput (ψ s j) g) _ r
    change (∫⁻ x, ‖glyzRawExtension Φs (glyzTimeTranslateAmplitude a (glyzSmoothGridShift s)) gs r x‖ₑ ^ (p : ℝ)) ≤
      ENNReal.ofReal (Cs s * r ^ σ) *
        (∑ i ∈ Finset.range (2 ^ F), ∫⁻ x,
          ‖glyzRawExtension Φs (glyzTimeTranslateAmplitude a (glyzSmoothGridShift s))
            (glyzDyadicInput F i gs) r x‖ₑ ^ (p : ℝ)) +
      ENNReal.ofReal (Cs s * r ^ (-Q)) * (∫⁻ y, ‖gs y‖ₑ) ^ (p : ℝ) at hdec
    rw [hparent, ← Fin.sum_univ_eq_sum_range] at hdec
    simp_rw [hchild] at hdec
    have hmass : (∫⁻ y, ‖gs y‖ₑ) = ∫⁻ y, ‖glyzColorInput (w s) g y‖ₑ := by
      rw [show gs = glyzTimeTranslateInput (glyzColorInput (w s) g)
          (glyzSmoothGridShift s) from glyzSmoothGridData_eq_timeTranslate F ψ s g]
      exact lintegral_enorm_glyzTimeTranslateInput _ _
    rw [hmass] at hdec
    apply hdec.trans
    apply add_le_add <;> apply mul_le_mul_left <;> apply ENNReal.ofReal_le_ofReal
    · exact mul_le_mul_of_nonneg_right (hCsC s) (Real.rpow_nonneg hr0.le _)
    · exact mul_le_mul_of_nonneg_right (hCsC s) (Real.rpow_nonneg hr0.le _)
  have htotal := glyzRawExtension_color_power_assembly volume hΦ ha hc w hw hw0 hsum hone hg r hp1
    (ENNReal.ofReal (C₀ * r ^ σ)) (ENNReal.ofReal (C₀ * r ^ (-Q))) E hcolor
  have hcard : (Fintype.card (Fin 5) : ℝ≥0∞) ^ ((p : ℝ) - 1) = ENNReal.ofReal B := by
    simp only [Fintype.card_fin, B]
    simpa only [ENNReal.ofReal_ofNat, Nat.cast_ofNat] using
      (ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 5) (sub_nonneg.mpr hp1))
  have hcoef (v : ℝ) : ENNReal.ofReal B * ENNReal.ofReal (C₀ * r ^ v) =
      ENNReal.ofReal ((B * C₀) * r ^ v) := by
    rw [← ENNReal.ofReal_mul hB.le]
    congr 1
    ring
  rw [hcard, mul_add, ← mul_assoc, ← mul_assoc, hcoef, hcoef] at htotal
  exact htotal

/-- A fixed smooth time cutoff yields actual smooth pieces on the five
shifted grids. The constant precedes the entire sequence of partitions. -/
theorem Family.exists_glyz_original_smooth_power {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ K)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hrange : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) (hsχ : tsupport χ ⊆ Icc (-1 : ℝ) 1)
    (hone : ∀ x t η, a (x, t, η) ≠ 0 → χ t = 1)
    (q : ℕ) {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε rmin rmax Q : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      let F := glyzVariableFinalDepth (d + 1) N + q
      ∃ ψ : Fin 5 → Fin (2 ^ F) → ℝ → ℝ,
      (∀ s j, ContDiff ℝ ∞ (ψ s j) ∧ HasCompactSupport (ψ s j) ∧
        tsupport (ψ s j) ⊆ tsupport χ ∧
        tsupport (ψ s j) ⊆ glyzShiftedOpenCell F (glyzSmoothGridShift s) j ∧
        ∀ t, 0 ≤ ψ s j t ∧ ψ s j t ≤ χ t) ∧
      (∀ t, ∑ s, ∑ j, ψ s j t = χ t) ∧
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
  obtain ⟨C, hC, hmain⟩ := G.exists_glyz_original_smooth_power_uniform hG ha hc hK hdet has
    q hp hε hrmin hQ (rmax := rmax)
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨ψ, hψ, hsum⟩ := exists_glyz_shifted_smooth_partition
    (glyzVariableFinalDepth (d + 1) N + q) χ hχ hcχ (fun t => (hrange t).1) hsχ
  refine ⟨ψ, hψ, hsum, ?_⟩
  exact hmain N ψ (fun s j => (hψ s j).1.continuous) (fun s j => (hψ s j).2.2.2.1)
    (fun s j t => ((hψ s j).2.2.2.2 t).1)
    (fun t => (hsum t).le.trans (hrange t).2)
    (fun x t η hn => (hsum t).trans (hone x t η hn))

end PlanarNikodym
