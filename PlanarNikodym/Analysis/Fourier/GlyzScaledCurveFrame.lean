import PlanarNikodym.Analysis.Fourier.GlyzCurveBoxTaylor
import PlanarNikodym.Analysis.Fourier.GlyzCurveJetInverse
import PlanarNikodym.Analysis.Fourier.GlyzMomentBoxRescaling

/-! Derivative-scaled frames for actual curves. Euclidean errors of size
delta^l are absorbed by a uniformly enlarged Fourier parallelepiped. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped BigOperators
namespace PlanarNikodym

def glyzScaledFrame {l : ℕ} (L : GlyzSpace l ≃L[ℝ] GlyzSpace l)
    (δ : ℝ) (hδ : 0 < δ) : GlyzSpace l ≃L[ℝ] GlyzSpace l :=
  (EuclideanSpace.equiv (Fin l) ℝ).trans
    ((coefficientDilation (fun j : Fin l => δ ^ ((j : ℕ) + 1))
      (fun _ => pow_ne_zero _ hδ.ne')).trans
        ((EuclideanSpace.equiv (Fin l) ℝ).symm.trans L))

theorem glyzScaledFrame_apply {l : ℕ} (L : GlyzSpace l ≃L[ℝ] GlyzSpace l)
    (δ : ℝ) (hδ : 0 < δ) (x : GlyzSpace l) :
    glyzScaledFrame L δ hδ x =
      L ((EuclideanSpace.equiv (Fin l) ℝ).symm
        (fun j => δ ^ ((j : ℕ) + 1) * x j)) := rfl

theorem glyzScaledFrame_symm_coord {l : ℕ} (L : GlyzSpace l ≃L[ℝ] GlyzSpace l)
    (δ : ℝ) (hδ : 0 < δ) (x : GlyzSpace l) (j : Fin l) :
    (glyzScaledFrame L δ hδ).symm x j =
      (δ ^ ((j : ℕ) + 1))⁻¹ * L.symm x j := rfl

theorem glyzCurveBox_eq_frequencyBox {l : ℕ} (γ : ℝ → GlyzSpace l) (s δ : ℝ)
    (hδ : 0 < δ) (L : GlyzSpace l ≃L[ℝ] GlyzSpace l)
    (hL : L.toContinuousLinearMap = glyzCurveJetOperator γ s) :
    glyzCurveBox γ l s δ = glyzFrequencyBox (glyzScaledFrame L δ hδ) (γ s) 1 := by
  rw [glyzFrequencyBox_eq_image]
  have hf : glyzCurveBoxPoint γ l s δ =
      fun v : Base l => γ s + glyzScaledFrame L δ hδ
        ((EuclideanSpace.equiv (Fin l) ℝ).symm v) := by
    funext v
    rw [glyzScaledFrame_apply]
    change _ = γ s + L.toContinuousLinearMap
      ((EuclideanSpace.equiv (Fin l) ℝ).symm (fun j => δ ^ ((j : ℕ) + 1) * v j))
    rw [hL, glyzCurveJetOperator_apply]
    rfl
  unfold glyzCurveBox
  rw [hf]
  congr 1
  ext v
  simp only [mem_setOf_eq, mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg zero_le_one, Real.norm_eq_abs]

theorem norm_glyzScaledFrame_symm_coordinates_le {l : ℕ}
    (L : GlyzSpace l ≃L[ℝ] GlyzSpace l) {δ C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : 0 ≤ C) (hL : ‖L.symm.toContinuousLinearMap‖ ≤ C) (x : GlyzSpace l) :
    ‖(EuclideanSpace.equiv (Fin l) ℝ) ((glyzScaledFrame L δ hδ).symm x)‖ ≤
      (δ ^ l)⁻¹ * (C * ‖x‖) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  change |(glyzScaledFrame L δ hδ).symm x j| ≤ _
  rw [glyzScaledFrame_symm_coord, abs_mul, abs_inv, abs_of_pos (pow_pos hδ _)]
  have hp : (δ ^ ((j : ℕ) + 1))⁻¹ ≤ (δ ^ l)⁻¹ :=
    inv_le_inv₀ (pow_pos hδ _) (pow_pos hδ _) |>.mpr
      (pow_le_pow_of_le_one hδ.le hδ1 j.isLt)
  calc
    _ ≤ (δ ^ l)⁻¹ * ‖L.symm x‖ :=
      mul_le_mul hp (PiLp.norm_apply_le (L.symm x) j) (abs_nonneg _) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((L.symm.toContinuousLinearMap.le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg x))) (by positivity)

theorem glyzFrequencyBox_absorb_error {l : ℕ}
    (L : GlyzSpace l ≃L[ℝ] GlyzSpace l) {δ C K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : 0 ≤ C) (hL : ‖L.symm.toContinuousLinearMap‖ ≤ C)
    (a ξ η : GlyzSpace l) (hη : η ∈ glyzFrequencyBox (glyzScaledFrame L δ hδ) a 1)
    (herr : ‖ξ - η‖ ≤ K * δ ^ l) :
    ξ ∈ glyzFrequencyBox (glyzScaledFrame L δ hδ) a (1 + C * K) := by
  let Q := (EuclideanSpace.equiv (Fin l) ℝ).toContinuousLinearMap.comp
    (glyzScaledFrame L δ hδ).symm.toContinuousLinearMap
  change ‖Q (ξ - a)‖ ≤ 1 + C * K
  change ‖Q (η - a)‖ ≤ 1 at hη
  have he : Q (ξ - a) = Q (η - a) + Q (ξ - η) := by
    rw [← map_add]
    congr 1
    abel
  have herror : ‖Q (ξ - η)‖ ≤ C * K := by
    calc
      _ ≤ (δ ^ l)⁻¹ * (C * ‖ξ - η‖) :=
        norm_glyzScaledFrame_symm_coordinates_le L hδ hδ1 hC hL _
      _ ≤ (δ ^ l)⁻¹ * (C * (K * δ ^ l)) := by gcongr
      _ = C * K := by field_simp
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hη herror)

end PlanarNikodym
