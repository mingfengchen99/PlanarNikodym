import PlanarNikodym.Analysis.Fourier.GlyzControlledCurveDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzBandlimitedLocalization

/-! Actual local weighted decoupling for the separated projected curves
in GLYZ. The only analytic induction premise is zero optimal loss for
the ordinary lower-dimensional moment curve. Both the global estimate
and the bandlimited localization are applied to genuine Schwartz pieces. -/
noncomputable section
open Set Metric MeasureTheory
open scoped FourierTransform BigOperators NNReal ENNReal
namespace PlanarNikodym

/-- Zero extension gives the global curve estimate for every subset of
the separated dyadic centers, with the same uniform coefficient. -/
theorem glyz_controlled_curve_subset_decoupling_of_moment_optimal_zero
    (l r : ℕ) {p : ℝ≥0} (hp : 1 ≤ p)
    (hη : glyzOptimalSquareLoss l p = 0)
    {ν Q ε : ℝ} (hν : 0 < ν) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (t : ℝ) (I : Finset ℕ)
      (f : ℕ → SchwartzMap (GlyzSpace l) ℂ),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, (glyzDyadicCenter N j, t) ∈ separatedMixedCenters ν) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      lpNorm ((∑ j ∈ I, f j : SchwartzMap (GlyzSpace l) ℂ) :
        GlyzSpace l → ℂ) p volume ^ 2 ≤
        C * (2 : ℝ) ^ (ε * N) *
          ∑ j ∈ I, lpNorm (f j : GlyzSpace l → ℂ) p volume ^ 2 := by
  classical
  obtain ⟨C, hC, hglobal⟩ :=
    glyz_controlled_curve_decoupling_of_moment_optimal_zero l r hp hη hν hQ hε
  refine ⟨C, hC, fun N t I f hI hsep hf => ?_⟩
  let g : ℕ → SchwartzMap (GlyzSpace l) ℂ := fun j => if j ∈ I then f j else 0
  have hgsep : ∀ j < 2 ^ N, g j ≠ 0 →
      (glyzDyadicCenter N j, t) ∈ separatedMixedCenters ν := by
    intro j _ hj
    by_cases hjI : j ∈ I
    · exact hsep j hjI
    · exact False.elim (hj (by simp [g, hjI]))
  have hgsupp : ∀ j < 2 ^ N, Function.support (𝓕 (g j : GlyzSpace l → ℂ)) ⊆
      glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
        (glyzDyadicCenter N j) (glyzDyadicScale N) Q := by
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
  have henergy : (∑ j ∈ Finset.range (2 ^ N), lpNorm (g j : GlyzSpace l → ℂ) p volume ^ 2) =
      ∑ j ∈ I, lpNorm (f j : GlyzSpace l → ℂ) p volume ^ 2 := by
    calc
      _ = ∑ j ∈ I, lpNorm (g j : GlyzSpace l → ℂ) p volume ^ 2 :=
        (Finset.sum_subset hI (fun j _ hj => by
          simp only [g, if_neg hj, FunLike.coe_zero, lpNorm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])).symm
      _ = _ := Finset.sum_congr rfl fun j hj => by simp only [g, if_pos hj]
  simpa only [hsum, henergy] using hglobal N t g hgsep hgsupp

/-- The actual weighted local GL4 estimate on the physical ball of radius
`δ^(-l)`, for `δ = 2^(-N)`. The coefficient precedes the depth, projected
curve, index subset and Schwartz family. Its epsilon loss is for the
p-th power integral, and may be arbitrarily small. -/
theorem glyz_controlled_curve_weighted_local_of_moment_optimal_zero
    (l r A : ℕ) {p : ℝ≥0} (hp : 1 ≤ p)
    (hη : glyzOptimalSquareLoss l p = 0)
    {ν Q ε : ℝ} (hν : 0 < ν) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (t : ℝ) (I : Finset ℕ)
      (f : ℕ → SchwartzMap (GlyzSpace l) ℂ),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, (glyzDyadicCenter N j, t) ∈ separatedMixedCenters ν) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x in closedBall (0 : GlyzSpace l) ((glyzDyadicScale N ^ l)⁻¹),
        ‖(∑ j ∈ I, f j) x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (ε * N)) *
          (∑ j ∈ I, (∫⁻ x, ‖f j x‖ₑ ^ (p : ℝ) *
            ENNReal.ofReal (glyzNormWeight A ((glyzDyadicScale N ^ l) • x))) ^
              (2 / (p : ℝ))) ^ ((p : ℝ) / 2) := by
  classical
  have hpR : (1 : ℝ) ≤ p := hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hpR
  obtain ⟨K, hK, hframe⟩ := exists_uniform_glyzCoordinateCurve_inverse l r hν
  obtain ⟨S, C₀, hS, hC₀, hlocal⟩ := exists_glyz_scaled_boxes_local_decoupling l A hpR
  let α : ℝ := 2 * ε / p
  have hα : 0 < α := by dsimp [α]; positivity
  have hQ' : 0 < Q + K * S := by positivity
  obtain ⟨B, hB, hglobal⟩ := glyz_controlled_curve_subset_decoupling_of_moment_optimal_zero
    l r hp hη hν hQ' hα
  refine ⟨B ^ ((p : ℝ) / 2) * C₀, mul_pos (Real.rpow_pos_of_pos hB _) hC₀,
    fun N t I f hI hsep hf => ?_⟩
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
  have h := hlocal (glyzDyadicScale N) hδ hδ1 K Q hK.le ℕ I L
    (fun j => glyzCoordinateCurve l r t (glyzDyadicCenter N j)) f
    (ENNReal.ofReal (B * (2 : ℝ) ^ (α * N)) ^ ((p : ℝ) / 2))
    (fun j hj => (hL j hj).2)
    (fun j hj => by rw [← hbox j hj Q hQ.le]; exact hf j hj) (by
      intro g hg
      have hbound := hglobal N t I g hI hsep (fun j hj => by
        rw [hbox j hj (Q + K * S) hQ'.le]
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

/-- Volume-normalized form of the same actual local estimate, directly
compatible with the local-average and lower-dimensional slicing APIs. -/
theorem glyz_controlled_curve_normalized_local_of_moment_optimal_zero
    (l r A : ℕ) {p : ℝ≥0} (hp : 1 ≤ p)
    (hη : glyzOptimalSquareLoss l p = 0)
    {ν Q ε : ℝ} (hν : 0 < ν) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (t : ℝ) (I : Finset ℕ)
      (f : ℕ → SchwartzMap (GlyzSpace l) ℂ),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, (glyzDyadicCenter N j, t) ∈ separatedMixedCenters ν) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x, ‖(∑ j ∈ I, f j) x‖ₑ ^ (p : ℝ)
        ∂glyzBallMeasure (GlyzSpace l) ((glyzDyadicScale N ^ l)⁻¹)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (ε * N)) *
          (∑ j ∈ I, (∫⁻ x, ‖f j x‖ₑ ^ (p : ℝ) *
            ((volume (closedBall (0 : GlyzSpace l) ((glyzDyadicScale N ^ l)⁻¹)))⁻¹ *
              ENNReal.ofReal (glyzNormWeight A ((glyzDyadicScale N ^ l) • x)))) ^
                (2 / (p : ℝ))) ^ ((p : ℝ) / 2) := by
  obtain ⟨C, hC, h⟩ := glyz_controlled_curve_weighted_local_of_moment_optimal_zero
    l r A hp hη hν hQ hε
  refine ⟨C, hC, fun N t I f hI hsep hf => ?_⟩
  exact glyz_normalize_local_decoupling I f (by positivity [glyzDyadicScale_pos N])
    (by exact_mod_cast lt_of_lt_of_le zero_lt_one hp)
    _ _ (h N t I f hI hsep hf)

end PlanarNikodym
