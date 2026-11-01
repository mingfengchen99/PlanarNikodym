import PlanarNikodym.Analysis.Fourier.GlyzProjectedCurve

/-! Uniform finite derivative bounds for the actual orthogonally
projected moment curves. The bound is independent of the projection
center, and includes every derivative up to any prescribed order. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace PlanarNikodym

theorem glyzMomentDerivative_norm_le (m n : ℕ) {s : ℝ} (hs : |s| ≤ 1) :
    ‖(fun k : Fin m => iteratedDeriv n (fun t : ℝ => t ^ ((k : ℕ) + 1)) s)‖ ≤
      ∑ k : Fin m, (((k : ℕ) + 1).descFactorial n : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun k _ => Nat.cast_nonneg _)).mpr
  intro k
  calc
    _ = (((k : ℕ) + 1).descFactorial n : ℝ) * |s| ^ (((k : ℕ) + 1) - n) := by
      rw [iteratedDeriv_pow, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs, abs_pow]
    _ ≤ (((k : ℕ) + 1).descFactorial n : ℝ) :=
      mul_le_of_le_one_right (Nat.cast_nonneg _) (pow_le_one₀ (abs_nonneg s) hs)
    _ ≤ _ := Finset.single_le_sum (f := fun j : Fin m => (((j : ℕ) + 1).descFactorial n : ℝ))
      (fun j _ => Nat.cast_nonneg _) (Finset.mem_univ k)

theorem norm_iteratedDeriv_glyzOrthogonalCurve_le (l r n : ℕ) {s : ℝ} (hs : |s| ≤ 1) (t : ℝ) :
    ‖iteratedDeriv n (glyzOrthogonalCurve l r t) s‖ ≤
      ‖(EuclideanSpace.equiv (Fin (l + r)) ℝ).symm.toContinuousLinearMap‖ *
        ∑ k : Fin (l + r), (((k : ℕ) + 1).descFactorial n : ℝ) := by
  let v : Base (l + r) := fun k => iteratedDeriv n (fun u : ℝ => u ^ ((k : ℕ) + 1)) s
  have he : iteratedDeriv n (glyzOrthogonalCurve l r t) s =
      (glyzEuclideanTangentSpace (l + r) r t)ᗮ.orthogonalProjectionOnto
        ((EuclideanSpace.equiv (Fin (l + r)) ℝ).symm v) :=
    iteratedDeriv_glyzMomentCurve_linear
      (((glyzEuclideanTangentSpace (l + r) r t)ᗮ.orthogonalProjectionOnto).comp
        (EuclideanSpace.equiv (Fin (l + r)) ℝ).symm.toContinuousLinearMap) _ _
  rw [he]
  exact ((glyzEuclideanTangentSpace (l + r) r t)ᗮ.norm_orthogonalProjectionOnto_apply_le _).trans
    (((EuclideanSpace.equiv (Fin (l + r)) ℝ).symm.toContinuousLinearMap.le_opNorm v).trans
      (mul_le_mul_of_nonneg_left (glyzMomentDerivative_norm_le (l + r) n hs) (norm_nonneg _)))

theorem exists_uniform_glyzOrthogonalCurve_derivative_bound (l r M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ∀ s ∈ Icc (-1 : ℝ) 1, ∀ n ≤ M,
      ‖iteratedDeriv n (glyzOrthogonalCurve l r t) s‖ ≤ C := by
  let B : ℝ := ∑ n ∈ Finset.range (M + 1),
    ∑ k : Fin (l + r), (((k : ℕ) + 1).descFactorial n : ℝ)
  let D := ‖(EuclideanSpace.equiv (Fin (l + r)) ℝ).symm.toContinuousLinearMap‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun k _ => Nat.cast_nonneg _
  have hD : 0 ≤ D := norm_nonneg _
  refine ⟨D * B + 1, by positivity, ?_⟩
  intro t s hs n hn
  have ha : |s| ≤ 1 := abs_le.mpr hs
  have hnB : (∑ k : Fin (l + r), (((k : ℕ) + 1).descFactorial n : ℝ)) ≤ B :=
    Finset.single_le_sum (s := Finset.range (M + 1))
      (f := fun j => ∑ k : Fin (l + r), (((k : ℕ) + 1).descFactorial j : ℝ))
      (fun j _ => Finset.sum_nonneg fun k _ => Nat.cast_nonneg _)
      (Finset.mem_range.mpr (by omega : n < M + 1))
  exact (norm_iteratedDeriv_glyzOrthogonalCurve_le l r n ha t).trans
    ((mul_le_mul_of_nonneg_left hnB hD).trans (by linarith))

end PlanarNikodym
