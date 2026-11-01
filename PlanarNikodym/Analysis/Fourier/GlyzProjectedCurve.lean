import PlanarNikodym.Analysis.Fourier.GlyzOrthogonalJets

/-! The actual orthogonally projected curve and its actual iterated
derivatives. Its first l derivatives have nonzero Gram determinant. -/
noncomputable section
open Set Submodule
open scoped BigOperators ContDiff
namespace PlanarNikodym

theorem glyz_linear_map_eq_sum {m : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : Base m →L[ℝ] F) (v : Base m) :
    L v = ∑ k : Fin m, v k • L (Pi.single k 1) := by
  calc
    _ = L (∑ k : Fin m, Pi.single k (v k)) := by rw [Finset.univ_sum_single]
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      have he : (Pi.single k (v k) : Base m) = v k • Pi.single k 1 := by
        ext j
        by_cases hj : j = k <;> simp [hj, Pi.smul_apply]
      rw [he, map_smul]

theorem iteratedDeriv_glyzMomentCurve_linear {m : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : Base m →L[ℝ] F) (n : ℕ) (s : ℝ) :
    iteratedDeriv n (fun t => L (glyzMomentCurve m t)) s =
      L (fun k => iteratedDeriv n (fun t => t ^ ((k : ℕ) + 1)) s) := by
  have he : (fun t => L (glyzMomentCurve m t)) =
      fun t => ∑ k : Fin m, t ^ ((k : ℕ) + 1) • L (Pi.single k 1) := by
    funext t
    exact glyz_linear_map_eq_sum L (glyzMomentCurve m t)
  rw [he, iteratedDeriv_fun_sum (fun k _ => by fun_prop)]
  calc
    _ = ∑ k : Fin m, iteratedDeriv n (fun t : ℝ => t ^ ((k : ℕ) + 1)) s • L (Pi.single k 1) := by
      apply Finset.sum_congr rfl
      intro k _
      exact iteratedDeriv_smul_const (f := fun t : ℝ => t ^ ((k : ℕ) + 1))
        (n := n) (x := s) (by fun_prop) _
    _ = _ := (glyz_linear_map_eq_sum L _).symm

def glyzOrthogonalCurve (l r : ℕ) (t : ℝ) (s : ℝ) :
    (glyzEuclideanTangentSpace (l + r) r t)ᗮ :=
  (glyzEuclideanTangentSpace (l + r) r t)ᗮ.orthogonalProjectionOnto
    ((EuclideanSpace.equiv (Fin (l + r)) ℝ).symm (glyzMomentCurve (l + r) s))

theorem contDiff_glyzOrthogonalCurve (l r : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (glyzOrthogonalCurve l r t) := by
  have hΓ : ContDiff ℝ ∞ (glyzMomentCurve (l + r)) := contDiff_pi.mpr fun k => contDiff_id.pow _
  exact ((glyzEuclideanTangentSpace (l + r) r t)ᗮ.orthogonalProjectionOnto).contDiff.comp
    ((EuclideanSpace.equiv (Fin (l + r)) ℝ).symm.contDiff.comp hΓ)

theorem iteratedDeriv_glyzOrthogonalCurve (l r : ℕ) (s t : ℝ) (j : Fin l) :
    iteratedDeriv ((j : ℕ) + 1) (glyzOrthogonalCurve l r t) s =
      glyzOrthogonalJetBlock l r s t j := by
  exact iteratedDeriv_glyzMomentCurve_linear
    (((glyzEuclideanTangentSpace (l + r) r t)ᗮ.orthogonalProjectionOnto).comp
      (EuclideanSpace.equiv (Fin (l + r)) ℝ).symm.toContinuousLinearMap) _ _

theorem det_gram_glyzOrthogonalCurve_ne_zero (l r : ℕ) {s t : ℝ} (hst : s ≠ t) :
    (Matrix.gram ℝ (fun j : Fin l =>
      iteratedDeriv ((j : ℕ) + 1) (glyzOrthogonalCurve l r t) s)).det ≠ 0 := by
  simp_rw [iteratedDeriv_glyzOrthogonalCurve]
  exact det_gram_glyzOrthogonalJets_ne_zero l r hst

end PlanarNikodym
