import PlanarNikodym.Analysis.Fourier.GlyzConeRadialPartition

/-! Euclidean Fourier thickening of actual cone boxes. At the physical
uncertainty scale, both the change of radius and the horizontal error
are absorbed into fixed enlargements, uniformly over the controlled
curve class. -/
noncomputable section
open Set Metric MeasureTheory
open scoped Pointwise BigOperators
namespace PlanarNikodym

theorem glyzConeBox_add_ball_subset {k : ℕ} (γ : ℝ → GlyzSpace k)
    (L : GlyzSpace k ≃L[ℝ] GlyzSpace k) {s δ R B C S rmin rmax : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hrmin : 0 < rmin)
    (hsmall : S * δ ^ k ≤ rmin / 2)
    (hder : ∀ j ≤ k, ‖iteratedDeriv j γ s‖ ≤ B)
    (hL : L.toContinuousLinearMap = glyzCurveJetOperator γ s)
    (hLi : ‖L.symm.toContinuousLinearMap‖ ≤ C) :
    glyzConeBox k γ s δ R rmin rmax + closedBall (0 : GlyzConeSpace k) (S * δ ^ k) ⊆
      glyzConeBox k γ s δ
        (R + C * ((2 / rmin) * S * (1 + (B + (k : ℝ) * R * B))))
        (rmin / 2) (rmax + rmin / 2) := by
  rintro z ⟨w, ⟨r, hr, ξ, hξ, rfl⟩, e, he, rfl⟩
  have he' : ‖e‖ ≤ S * δ ^ k := by simpa only [mem_closedBall, dist_zero_right] using he
  have heu : ‖(WithLp.ofLp e).1‖ ≤ S * δ ^ k := (WithLp.norm_fst_le (GlyzSpace k) e).trans he'
  have hev : |(WithLp.ofLp e).2| ≤ S * δ ^ k :=
    (show |(WithLp.ofLp e).2| ≤ ‖e‖ by
      simpa only [Real.norm_eq_abs, WithLp.ofLp_snd] using
        WithLp.norm_snd_le (GlyzSpace k) e).trans he'
  let r' := r + (WithLp.ofLp e).2
  have hr' : r' ∈ Icc (rmin / 2) (rmax + rmin / 2) := by
    have h := abs_le.mp (hev.trans hsmall)
    constructor
    · change rmin / 2 ≤ r + (WithLp.ofLp e).2
      linarith [h.1, hr.1]
    · change r + (WithLp.ofLp e).2 ≤ rmax + rmin / 2
      linarith [h.2, hr.2]
  have hr'0 : 0 < r' := (half_pos hrmin).trans_le hr'.1
  let H := B + (k : ℝ) * R * B
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hξnorm : ‖ξ‖ ≤ H := glyzEnlargedCurveBox_norm_le γ hδ.le hδ1 hR hB hder hξ
  let u := r'⁻¹ • ((WithLp.ofLp e).1 - (WithLp.ofLp e).2 • ξ)
  let K := (2 / rmin) * S * (1 + H)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hu : ‖u‖ ≤ K * δ ^ k := by
    have hi : r'⁻¹ ≤ 2 / rmin := by
      rw [← one_div]
      apply (div_le_iff₀ hr'0).mpr
      have h := mul_le_mul_of_nonneg_left hr'.1 (show 0 ≤ 2 / rmin by positivity)
      have heq : (2 / rmin) * (rmin / 2) = 1 := by field_simp
      linarith
    change ‖r'⁻¹ • ((WithLp.ofLp e).1 - (WithLp.ofLp e).2 • ξ)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr'0)]
    calc
      _ ≤ r'⁻¹ * (‖(WithLp.ofLp e).1‖ + ‖(WithLp.ofLp e).2 • ξ‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hr'0.le)
      _ ≤ (2 / rmin) * (S * δ ^ k + (S * δ ^ k) * H) := by
        apply mul_le_mul hi _ (by positivity) (by positivity)
        apply add_le_add heu
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul hev hξnorm (norm_nonneg _) (by positivity)
      _ = K * δ ^ k := by dsimp [K]; ring
  have hξ' : ξ + u ∈ glyzEnlargedCurveBox γ k s δ (R + C * K) := by
    rw [glyzEnlargedCurveBox_eq_frequencyBox γ s δ _ hδ (by positivity) L hL]
    have hξbox : ξ ∈ glyzFrequencyBox (glyzScaledFrame L δ hδ) (γ s) R := by
      rwa [glyzEnlargedCurveBox_eq_frequencyBox γ s δ R hδ hR L hL] at hξ
    exact glyz_scaled_box_add_ball_subset L hδ hδ1 hC hLi (γ s)
      ⟨ξ, hξbox, u, by simpa only [mem_closedBall, dist_zero_right] using hu, rfl⟩
  refine ⟨r', hr', ξ + u, hξ', ?_⟩
  have hprod : r' • (ξ + u) = r • ξ + (WithLp.ofLp e).1 := by
    dsimp [u]
    rw [smul_add, smul_smul, mul_inv_cancel₀ hr'0.ne', one_smul]
    dsimp [r']
    rw [add_smul]
    abel
  apply WithLp.ofLp_injective
  change (r • ξ, r) + WithLp.ofLp e = (r' • (ξ + u), r')
  rw [hprod]
  rfl

/-- Uniform enlargement follows from actual derivative and determinant
bounds. No regularity stronger than those pointwise data is needed. -/
theorem exists_uniform_glyz_cone_thickening (k : ℕ) {β B R S rmin : ℝ}
    (hβ : 0 < β) (hB : 0 < B) (hR : 0 < R) (hS : 0 < S) (hrmin : 0 < rmin) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ (γ : ℝ → GlyzSpace k) (s δ rmax : ℝ),
      0 < δ → δ ≤ 1 → S * δ ^ k ≤ rmin / 2 →
      (∀ j ≤ k, ‖iteratedDeriv j γ s‖ ≤ B) →
      β ≤ |(glyzCurveJetOperator γ s).det| →
      glyzConeBox k γ s δ R rmin rmax + closedBall (0 : GlyzConeSpace k) (S * δ ^ k) ⊆
        glyzConeBox k γ s δ Q (rmin / 2) (rmax + rmin / 2) := by
  obtain ⟨C, hC, hframe⟩ := exists_uniform_glyz_general_curve_inverse k hβ hB
  refine ⟨R + C * ((2 / rmin) * S * (1 + (B + (k : ℝ) * R * B))), by positivity,
    fun γ s δ rmax hδ hδ1 hsmall hder hdet => ?_⟩
  obtain ⟨L, hL, hLi⟩ := hframe γ s (fun j => hder _ (by omega)) hdet
  exact glyzConeBox_add_ball_subset γ L hδ hδ1 hR.le hB.le hC.le hS.le hrmin
    hsmall hder hL hLi

end PlanarNikodym
