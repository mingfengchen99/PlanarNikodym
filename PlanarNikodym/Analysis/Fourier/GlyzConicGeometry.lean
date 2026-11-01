import PlanarNikodym.Analysis.Fourier.GlyzGeneralTaylorNesting
import PlanarNikodym.Analysis.Fourier.GlyzCylindricalMoment

/-! Actual conic affine coordinates and radial truncation. The shear
keeps the radial coordinate and normalizes the horizontal Taylor model.
A sufficiently narrow radial interval projects into enlarged moment boxes
with a radius independent of the angular refinement depth. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators FourierTransform NNReal ENNReal
namespace PlanarNikodym

abbrev GlyzConeSpace (k : ℕ) := WithLp 2 (GlyzSpace k × ℝ)

def glyzConicProductEquiv {k : ℕ}
    (L : GlyzSpace k ≃L[ℝ] GlyzSpace k) (v : GlyzSpace k) :
    (GlyzSpace k × ℝ) ≃ₗ[ℝ] (GlyzSpace k × ℝ) where
  toFun z := (L z.1 + z.2 • v, z.2)
  invFun z := (L.symm (z.1 - z.2 • v), z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z w := by ext <;> simp [add_smul]; abel
  map_smul' c z := by ext <;> simp [smul_add, smul_smul]

def glyzConicEquiv {k : ℕ}
    (L : GlyzSpace k ≃L[ℝ] GlyzSpace k) (v : GlyzSpace k) :
    GlyzConeSpace k ≃L[ℝ] GlyzConeSpace k :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (GlyzSpace k) ℝ).trans
    ((glyzConicProductEquiv L v).toContinuousLinearEquiv.trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ (GlyzSpace k) ℝ).symm)

@[simp] theorem glyzConicEquiv_apply {k : ℕ}
    (L : GlyzSpace k ≃L[ℝ] GlyzSpace k) (v x : GlyzSpace k) (r : ℝ) :
    glyzConicEquiv L v (WithLp.toLp 2 (x, r)) =
      WithLp.toLp 2 (L x + r • v, r) := rfl

@[simp] theorem glyzConicEquiv_symm_apply {k : ℕ}
    (L : GlyzSpace k ≃L[ℝ] GlyzSpace k) (v x : GlyzSpace k) (r : ℝ) :
    (glyzConicEquiv L v).symm (WithLp.toLp 2 (x, r)) =
      WithLp.toLp 2 (L.symm (x - r • v), r) := rfl

/-- An affine base curve lifts to a linear change of cone coordinates. -/
theorem glyzConicEquiv_cone_point {k : ℕ}
    (L : GlyzSpace k ≃L[ℝ] GlyzSpace k) (v x : GlyzSpace k) (r : ℝ) :
    (glyzConicEquiv L v).symm (WithLp.toLp 2 (r • (v + L x), r)) =
      WithLp.toLp 2 (r • x, r) := by
  rw [glyzConicEquiv_symm_apply]
  simp [smul_add]

/-- Scaling a box by a scalar near one only enlarges its coefficient
radius; the displacement of its center is measured in the actual frame. -/
theorem glyzFrequencyBox_smul_subset {k : ℕ}
    (L : GlyzSpace k ≃L[ℝ] GlyzSpace k) (a : GlyzSpace k)
    {R T S t : ℝ} (hT : |t| ≤ T)
    (hS : |t - 1| * ‖(EuclideanSpace.equiv (Fin k) ℝ) (L.symm a)‖ ≤ S) :
    (fun ξ => t • ξ) '' glyzFrequencyBox L a R ⊆
      glyzFrequencyBox L a (T * R + S) := by
  rintro _ ⟨ξ, hξ, rfl⟩
  let Q := L.symm.trans (EuclideanSpace.equiv (Fin k) ℝ)
  change ‖Q (t • ξ - a)‖ ≤ T * R + S
  have he : t • ξ - a = t • (ξ - a) + (t - 1) • a := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [he, map_add, map_smul, map_smul]
  calc
    _ ≤ ‖t • Q (ξ - a)‖ + ‖(t - 1) • Q a‖ := norm_add_le _ _
    _ = |t| * ‖Q (ξ - a)‖ + |t - 1| * ‖Q a‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ T * R + S := add_le_add
      (mul_le_mul hT hξ (norm_nonneg _) (le_trans (abs_nonneg _) hT)) hS

/-- At one fixed angular depth, a positive radial width works for all
children. The enlarged box radius is independent of that depth. -/
theorem exists_glyz_moment_radial_width (k q : ℕ) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧
      ∀ i ∈ Finset.range (2 ^ q), ∀ t : ℝ, |t - 1| ≤ σ → ∀ R : ℝ,
      (fun ξ => t • ξ) ''
        glyzFrequencyBox (glyzMomentFrequencyFrame k (glyzDyadicCenter q i)
          (glyzDyadicScale q) (glyzDyadicScale_pos q))
          ((EuclideanSpace.equiv (Fin k) ℝ).symm
            (glyzMomentCurve k (glyzDyadicCenter q i))) R ⊆
        glyzFrequencyBox (glyzMomentFrequencyFrame k (glyzDyadicCenter q i)
          (glyzDyadicScale q) (glyzDyadicScale_pos q))
          ((EuclideanSpace.equiv (Fin k) ℝ).symm
            (glyzMomentCurve k (glyzDyadicCenter q i))) (2 * R + 1) := by
  classical
  let M : ℕ → ℝ := fun i => ‖(EuclideanSpace.equiv (Fin k) ℝ)
    ((glyzMomentFrequencyFrame k (glyzDyadicCenter q i)
      (glyzDyadicScale q) (glyzDyadicScale_pos q)).symm
        ((EuclideanSpace.equiv (Fin k) ℝ).symm
          (glyzMomentCurve k (glyzDyadicCenter q i))))‖
  let B := ∑ i ∈ Finset.range (2 ^ q), M i
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let σ : ℝ := min (1 / 2) (1 / (B + 1))
  have hσ : 0 < σ := lt_min (by norm_num) (by positivity)
  refine ⟨σ, hσ, min_le_left _ _, fun i hi t ht R => ?_⟩
  apply glyzFrequencyBox_smul_subset
  · have h := abs_le.mp (ht.trans (min_le_left _ _))
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hiB : M i ≤ B := Finset.single_le_sum (f := M)
      (fun j _ => show 0 ≤ M j from norm_nonneg _) hi
    have hsmall : σ * (B + 1) ≤ 1 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    change |t - 1| * M i ≤ 1
    exact (mul_le_mul ht (hiB.trans (le_add_of_nonneg_right zero_le_one))
      (norm_nonneg _) hσ.le).trans hsmall

end PlanarNikodym
