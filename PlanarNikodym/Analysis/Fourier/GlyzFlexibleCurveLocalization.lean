import PlanarNikodym.Analysis.Fourier.GlyzControlledCurveLocalization

/-! Local decoupling on balls with a controlled inverse radius.
This form handles dyadic rounding directly: the physical inverse radius
need only be bounded by a fixed multiple of the shortest Fourier side. -/
noncomputable section
open Set Metric MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem exists_glyz_scaled_boxes_flexible_local_decoupling (l A : ℕ) {p : ℝ} (hp : 1 ≤ p) (F : ℝ) (_hF : 0 < F) :
    ∃ S C : ℝ, 0 < S ∧ 0 < C ∧
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → ∀ (b : ℝ), 0 < b → b ≤ F * δ ^ l →
      ∀ (K T : ℝ), 0 ≤ K → ∀ (ι : Type*) (s : Finset ι)
      (L : ι → GlyzSpace l ≃L[ℝ] GlyzSpace l) (a : ι → GlyzSpace l)
      (f : ι → SchwartzMap (GlyzSpace l) ℂ) (D : ℝ≥0∞),
      (∀ i ∈ s, ‖(L i).symm.toContinuousLinearMap‖ ≤ K) →
      (∀ i ∈ s, Function.support (𝓕 (f i : GlyzSpace l → ℂ)) ⊆
        glyzFrequencyBox (glyzScaledFrame (L i) δ hδ) (a i) T) →
      (∀ g : ι → SchwartzMap (GlyzSpace l) ℂ,
        (∀ i ∈ s, Function.support (𝓕 (g i : GlyzSpace l → ℂ)) ⊆
          glyzFrequencyBox (glyzScaledFrame (L i) δ hδ) (a i) (T + K * (S * F))) →
        (∫⁻ x, ‖(∑ i ∈ s, g i) x‖ₑ ^ p) ≤ D *
          (∑ i ∈ s, (∫⁻ x, ‖g i x‖ₑ ^ p) ^ (2 / p)) ^ (p / 2)) →
      (∫⁻ x in closedBall (0 : GlyzSpace l) b⁻¹, ‖(∑ i ∈ s, f i) x‖ₑ ^ p) ≤
        D * ENNReal.ofReal C *
          (∑ i ∈ s, (∫⁻ x, ‖f i x‖ₑ ^ p *
            ENNReal.ofReal (glyzNormWeight A (b • x))) ^ (2 / p)) ^ (p / 2) := by
  obtain ⟨S, C, hS, hC, hlocal⟩ :=
    exists_glyz_global_to_weighted_local_decoupling (E := GlyzSpace l) A hp
  refine ⟨S, C, hS, hC, fun δ hδ hδ1 b hb hbδ K T hK ι s L a f D hL hf hglobal => ?_⟩
  have h := hlocal b⁻¹ (inv_pos.mpr hb) ι s f
    (fun i => glyzFrequencyBox (glyzScaledFrame (L i) δ hδ) (a i) T) D hf ?_
  · simpa only [inv_inv] using h
  · intro g hg
    apply hglobal g
    intro i hi
    apply (hg i hi).trans
    rw [div_inv_eq_mul]
    exact (add_subset_add (Subset.refl _) (closedBall_subset_closedBall
      (show S * b ≤ (S * F) * δ ^ l by nlinarith))).trans
        (glyz_scaled_box_add_ball_subset (L i) hδ hδ1 hK (hL i hi) (a i))


theorem glyz_controlled_curve_flexible_local_of_moment_optimal_zero
    (l r A : ℕ) {p : ℝ≥0} (hp : 1 ≤ p)
    (hη : glyzOptimalSquareLoss l p = 0) (F : ℝ) (hF : 0 < F)
    {ν Q ε : ℝ} (hν : 0 < ν) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (t : ℝ) (I : Finset ℕ)
      (f : ℕ → SchwartzMap (GlyzSpace l) ℂ) (b : ℝ),
      0 < b → b ≤ F * glyzDyadicScale N ^ l →
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, (glyzDyadicCenter N j, t) ∈ separatedMixedCenters ν) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x in closedBall (0 : GlyzSpace l) b⁻¹,
        ‖(∑ j ∈ I, f j) x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (ε * N)) *
          (∑ j ∈ I, (∫⁻ x, ‖f j x‖ₑ ^ (p : ℝ) *
            ENNReal.ofReal (glyzNormWeight A (b • x))) ^
              (2 / (p : ℝ))) ^ ((p : ℝ) / 2) := by
  classical
  have hpR : (1 : ℝ) ≤ p := hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hpR
  obtain ⟨K, hK, hframe⟩ := exists_uniform_glyzCoordinateCurve_inverse l r hν
  obtain ⟨S, C₀, hS, hC₀, hlocal⟩ := exists_glyz_scaled_boxes_flexible_local_decoupling l A hpR F hF
  let α : ℝ := 2 * ε / p
  have hα : 0 < α := by dsimp [α]; positivity
  have hQ' : 0 < Q + K * (S * F) := by positivity
  obtain ⟨B, hB, hglobal⟩ := glyz_controlled_curve_subset_decoupling_of_moment_optimal_zero
    l r hp hη hν hQ' hα
  refine ⟨B ^ ((p : ℝ) / 2) * C₀, mul_pos (Real.rpow_pos_of_pos hB _) hC₀,
    fun N t I f b hb hbδ hI hsep hf => ?_⟩
  have hδ := glyzDyadicScale_pos N
  have hδ1 : glyzDyadicScale N ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hframes (j : ℕ) : ∃ L : GlyzSpace l ≃L[ℝ] GlyzSpace l,
      j ∈ I → L.toContinuousLinearMap =
        glyzCurveJetOperator (glyzCoordinateCurve l r t) (glyzDyadicCenter N j) ∧
        ‖L.symm.toContinuousLinearMap‖ ≤ K := by
    by_cases hj : j ∈ I
    · obtain ⟨L, hL, hnorm⟩ := hframe (glyzDyadicCenter N j, t) (hsep j hj)
      exact ⟨L, fun _ => ⟨hL, hnorm⟩⟩
    · exact ⟨ContinuousLinearEquiv.refl ℝ (GlyzSpace l), fun hj' => False.elim (hj hj')⟩
  choose L hL using hframes
  have hbox (j : ℕ) (hj : j ∈ I) (T : ℝ) (hT : 0 ≤ T) :
      glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
        (glyzDyadicCenter N j) (glyzDyadicScale N) T =
      glyzFrequencyBox (glyzScaledFrame (L j) (glyzDyadicScale N) hδ)
        (glyzCoordinateCurve l r t (glyzDyadicCenter N j)) T :=
    glyzEnlargedCurveBox_eq_frequencyBox _ _ _ _ hδ hT (L j) (hL j hj).1
  have h := hlocal (glyzDyadicScale N) hδ hδ1 b hb hbδ K Q hK.le ℕ I L
    (fun j => glyzCoordinateCurve l r t (glyzDyadicCenter N j)) f
    (ENNReal.ofReal (B * (2 : ℝ) ^ (α * N)) ^ ((p : ℝ) / 2))
    (fun j hj => (hL j hj).2)
    (fun j hj => by rw [← hbox j hj Q hQ.le]; exact hf j hj) (by
      intro g hg
      have hbound := hglobal N t I g hI hsep (fun j hj => by
        rw [hbox j hj (Q + K * (S * F)) hQ'.le]
        exact hg j hj)
      exact glyz_square_decoupling_to_power_integrals I g
        (show 0 < p from hp0) (by positivity) hbound)
  have hcoef : ENNReal.ofReal (B * (2 : ℝ) ^ (α * N)) ^ ((p : ℝ) / 2) *
      ENNReal.ofReal C₀ =
      ENNReal.ofReal ((B ^ ((p : ℝ) / 2) * C₀) * (2 : ℝ) ^ (ε * N)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ B * (2 : ℝ) ^ (α * N))
      (by positivity : 0 ≤ (p : ℝ) / 2),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow hB.le (by positivity), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have he : (α * (N : ℝ)) * ((p : ℝ) / 2) = ε * N := by
      dsimp [α]
      field_simp [hp0.ne']
    rw [he]
    ring
  simpa only [hcoef] using h


end PlanarNikodym
