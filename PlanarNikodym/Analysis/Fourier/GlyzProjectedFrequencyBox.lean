import PlanarNikodym.Analysis.Fourier.GlyzTaylorFrequencyImage
import PlanarNikodym.Analysis.Fourier.GlyzFourierSlice

/-! The projection of an actual ambient moment box is contained in a
uniformly enlarged derivative box of the actual projected curve. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory FourierTransform Real
open scoped BigOperators FourierTransform
namespace PlanarNikodym

def glyzCoordinateProjection (l r : ℕ) (t : ℝ) : GlyzSpace (l + r) →L[ℝ] GlyzSpace l :=
  (glyzOrthogonalCoordinates l r t).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (glyzEuclideanTangentSpace (l + r) r t)ᗮ.orthogonalProjectionOnto

theorem glyzCoordinateProjection_jet (l r : ℕ) (t s : ℝ) (j : Fin (l + r)) :
    glyzCoordinateProjection l r t (glyzEuclideanJetBlock (l + r) (l + r) s j) =
      iteratedDeriv ((j : ℕ) + 1) (glyzCoordinateCurve l r t) s := by
  symm
  exact iteratedDeriv_glyzMomentCurve_linear
    ((glyzCoordinateProjection l r t).comp
      (EuclideanSpace.equiv (Fin (l + r)) ℝ).symm.toContinuousLinearMap) _ _

theorem glyzProjectedBox_tail_bound (l r : ℕ) (t s δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (v : Base (l + r)) (hv : ∀ j, |v j| ≤ 1) {B : ℝ}
    (hj : ∀ n ≤ l + r, ‖iteratedDeriv n (glyzCoordinateCurve l r t) s‖ ≤ B) :
    ‖glyzCoordinateProjection l r t
        ((EuclideanSpace.equiv (Fin (l + r)) ℝ).symm (glyzMomentCurve (l + r) s) +
          ∑ j : Fin (l + r), (δ ^ ((j : ℕ) + 1) * v j) • glyzEuclideanJetBlock (l + r) (l + r) s j) -
      glyzCurveBoxPoint (glyzCoordinateCurve l r t) l s δ (fun j => v (j.castAdd r))‖ ≤
        ((r : ℝ) * B) * δ ^ l := by
  rw [map_add, map_sum]
  simp_rw [map_smul, glyzCoordinateProjection_jet]
  change ‖glyzCoordinateCurve l r t s +
    (∑ j : Fin (l + r), (δ ^ ((j : ℕ) + 1) * v j) •
      iteratedDeriv ((j : ℕ) + 1) (glyzCoordinateCurve l r t) s) - _‖ ≤ _
  rw [Fin.sum_univ_add]
  have he : glyzCoordinateCurve l r t s +
      ((∑ j : Fin l, (δ ^ (((j.castAdd r : Fin (l + r)) : ℕ) + 1) * v (j.castAdd r)) •
        iteratedDeriv ((j.castAdd r : Fin (l + r)) : ℕ).succ (glyzCoordinateCurve l r t) s) +
       ∑ j : Fin r, (δ ^ ((j.natAdd l : Fin (l + r)) : ℕ).succ * v (j.natAdd l)) •
        iteratedDeriv ((j.natAdd l : Fin (l + r)) : ℕ).succ (glyzCoordinateCurve l r t) s) -
      glyzCurveBoxPoint (glyzCoordinateCurve l r t) l s δ (fun j => v (j.castAdd r)) =
      ∑ j : Fin r, (δ ^ ((j.natAdd l : Fin (l + r)) : ℕ).succ * v (j.natAdd l)) •
        iteratedDeriv ((j.natAdd l : Fin (l + r)) : ℕ).succ (glyzCoordinateCurve l r t) s := by
    unfold glyzCurveBoxPoint
    simp only [Fin.val_castAdd, Nat.succ_eq_add_one]
    abel
  rw [he]
  calc
    _ ≤ ∑ j : Fin r, ‖(δ ^ ((j.natAdd l : Fin (l + r)) : ℕ).succ * v (j.natAdd l)) •
        iteratedDeriv ((j.natAdd l : Fin (l + r)) : ℕ).succ (glyzCoordinateCurve l r t) s‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin r, δ ^ l * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hδ _)]
      have hp : δ ^ ((j.natAdd l : Fin (l + r)) : ℕ).succ ≤ δ ^ l :=
        pow_le_pow_of_le_one hδ.le hδ1 (by simp only [Fin.val_natAdd]; omega)
      have hv' : δ ^ ((j.natAdd l : Fin (l + r)) : ℕ).succ * |v (j.natAdd l)| ≤ δ ^ l :=
        (mul_le_of_le_one_right (pow_pos hδ _).le (hv _)).trans hp
      exact mul_le_mul hv' (hj _ (by simp only [Fin.val_natAdd]; omega))
        (norm_nonneg _) (pow_pos hδ _).le
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem exists_uniform_glyz_projected_frequencyBox (l r : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ separatedMixedCenters ν,
      ∃ L : GlyzSpace l ≃L[ℝ] GlyzSpace l,
        L.toContinuousLinearMap = glyzCurveJetOperator (glyzCoordinateCurve l r z.2) z.1 ∧
        ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
          glyzCoordinateProjection l r z.2 '' glyzMomentFrequencyBox (l + r) z.1 δ hδ ⊆
            glyzFrequencyBox (glyzScaledFrame L δ hδ) (glyzCoordinateCurve l r z.2 z.1) R := by
  obtain ⟨C, hC, hinv⟩ := exists_uniform_glyzCoordinateCurve_inverse l r hν
  obtain ⟨b, B, hb, hB, _, hder, _⟩ := exists_uniform_glyzCoordinateCurve_certificate l r (l + r) hν
  refine ⟨1 + C * ((r : ℝ) * B), by positivity, ?_⟩
  intro z hz
  obtain ⟨L, hL, hLi⟩ := hinv z hz
  refine ⟨L, hL, ?_⟩
  intro δ hδ hδ1 ξ hξ
  obtain ⟨η, hη, rfl⟩ := hξ
  rw [glyzMomentFrequencyBox_eq_generators] at hη
  obtain ⟨v, hv, rfl⟩ := hη
  apply glyzFrequencyBox_absorb_error L hδ hδ1 hC.le hLi _ _
    (glyzCurveBoxPoint (glyzCoordinateCurve l r z.2) l z.1 δ (fun j => v (j.castAdd r)))
  · rw [← glyzCurveBox_eq_frequencyBox _ _ _ hδ L hL]
    exact ⟨_, fun j => hv (j.castAdd r), rfl⟩
  · exact glyzProjectedBox_tail_bound l r z.2 z.1 δ hδ hδ1 v hv
      (hder z.2 z.1 hz.1)

end PlanarNikodym
