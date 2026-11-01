import PlanarNikodym.Analysis.Fourier.GlyzProjectiveCurve
import PlanarNikodym.Analysis.Fourier.TaylorJetNondegeneracy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The actual time-jet parameter minor is the full-jet determinant of
the frozen spatial-gradient curve. Mixed derivatives are commuted using
smoothness, then the projective chart is constructed from that minor. -/
noncomputable section
open Set Filter
open scoped BigOperators ContDiff Topology
namespace PlanarNikodym

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

 theorem glyz_smooth_directional_derivatives_commute
    (f : P → ℝ) (hf : ContDiff ℝ ∞ f) (x u v : P) :
    fderiv ℝ (fun y => fderiv ℝ f y u) x v =
      fderiv ℝ (fun y => fderiv ℝ f y v) x u := by
  have hdSmooth : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    hdSmooth.differentiable (by simp) x
  rw [fderiv_clm_apply hd (differentiableAt_const u),
    fderiv_clm_apply hd (differentiableAt_const v)]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using hf.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞); exact WithTop.coe_le_coe.mpr le_top) v u

theorem glyz_partialTimeDeriv_eq_fderiv (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (x : P × ℝ) : partialTimeDeriv Φ x = fderiv ℝ Φ x (0, 1) := by
  change fderiv ℝ (fun t => Φ (x.1, t)) x.2 1 = _
  rw [fderiv_snd_slice Φ x (hΦ.differentiable (by simp) x)]
  rfl

theorem glyz_partialTimeDeriv_directional (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (v : P × ℝ) (x : P × ℝ) :
    partialTimeDeriv (fun y => fderiv ℝ Φ y v) x = fderiv ℝ (partialTimeDeriv Φ) x v := by
  have hD : ContDiff ℝ ∞ (fun y => fderiv ℝ Φ y v) :=
    (hΦ.fderiv_right (by simp : ∞ + 1 ≤ ∞)).clm_apply contDiff_const
  rw [glyz_partialTimeDeriv_eq_fderiv _ hD]
  have he : partialTimeDeriv Φ = fun y => fderiv ℝ Φ y (0, 1) :=
    funext (glyz_partialTimeDeriv_eq_fderiv Φ hΦ)
  rw [he]
  exact glyz_smooth_directional_derivatives_commute Φ hΦ x v (0, 1)

theorem glyz_iteratedPartialTimeDeriv_directional (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (n : ℕ) (v : P × ℝ) (x : P × ℝ) :
    iteratedPartialTimeDeriv n (fun y => fderiv ℝ Φ y v) x =
      fderiv ℝ (iteratedPartialTimeDeriv n Φ) x v := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have he : iteratedPartialTimeDeriv n (fun y => fderiv ℝ Φ y v) =
        fun y => fderiv ℝ (iteratedPartialTimeDeriv n Φ) y v := by
      funext y
      exact ih y
    change partialTimeDeriv (iteratedPartialTimeDeriv n (fun y => fderiv ℝ Φ y v)) x = _
    rw [he]
    exact glyz_partialTimeDeriv_directional _
      (contDiff_iff_contDiffAt.mpr fun y => contDiffAt_iteratedPartialTimeDeriv hΦ.contDiffAt n) v x

/-- Actual spatial directional derivatives of the original phase,
retaining the time variable. -/
def glyzFrozenDirectionalCurve (k : ℕ) (Φ : P × ℝ → ℝ)
    (v : Fin (k + 1) → P) (w : P) (t : ℝ) : GlyzSpace (k + 1) :=
  WithLp.toLp 2 (fun j => fderiv ℝ Φ (w, t) (v j, 0))

theorem contDiff_glyzFrozenDirectionalCurve (k : ℕ) (Φ : P × ℝ → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (v : Fin (k + 1) → P) (w : P) :
    ContDiff ℝ ∞ (glyzFrozenDirectionalCurve k Φ v w) := by
  apply (EuclideanSpace.equiv (Fin (k + 1)) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro j
  exact (((hΦ.fderiv_right (by simp : ∞ + 1 ≤ ∞)).clm_apply
    (contDiff_const (c := (v j, 0)))).comp (contDiff_const.prodMk contDiff_id))

theorem glyzFrozenDirectionalCurve_jet_entry (k : ℕ) (Φ : P × ℝ → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (v : Fin (k + 1) → P) (w : P) (t : ℝ)
    (i j : Fin (k + 1)) :
    iteratedDeriv (i : ℕ) (glyzFrozenDirectionalCurve k Φ v w) t j =
      timeJetParameterMatrix Φ (k + 1) v t w i j := by
  have hΓ := contDiff_glyzFrozenDirectionalCurve k Φ hΦ v w
  have hproj := glyz_iteratedDeriv_comp_clm (EuclideanSpace.proj (𝕜 := ℝ) j)
    (glyzFrozenDirectionalCurve k Φ v w) t i
    (hΓ.of_le (by exact_mod_cast (le_top : ((i : ℕ) : ℕ∞) ≤ ⊤))).contDiffAt
  have hD : ContDiff ℝ ∞ (iteratedPartialTimeDeriv i Φ) :=
    contDiff_iff_contDiffAt.mpr fun y => contDiffAt_iteratedPartialTimeDeriv hΦ.contDiffAt i
  change _ = fderiv ℝ (fun q => iteratedDeriv i (fun s => Φ (q, s)) t) w (v j)
  change (EuclideanSpace.proj (𝕜 := ℝ) j) (iteratedDeriv (i : ℕ) (glyzFrozenDirectionalCurve k Φ v w) t) = _
  rw [← hproj]
  change iteratedDeriv i (fun s => fderiv ℝ Φ (w, s) (v j, 0)) t = _
  rw [← iteratedPartialTimeDeriv_apply i (fun y => fderiv ℝ Φ y (v j, 0)) w t,
    glyz_iteratedPartialTimeDeriv_directional Φ hΦ i (v j, 0) (w, t)]
  have he : (fun q => iteratedDeriv i (fun s => Φ (q, s)) t) =
      fun q => iteratedPartialTimeDeriv i Φ (q, t) := by
    funext q
    exact (iteratedPartialTimeDeriv_apply i Φ q t).symm
  rw [he, fderiv_fst_slice _ (w, t) (hD.differentiable (by simp) (w, t))]
  rfl

theorem det_glyzFrozenDirectionalCurve_fullJet (k : ℕ) (Φ : P × ℝ → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (v : Fin (k + 1) → P) (w : P) (t : ℝ) :
    (glyzCurveFullJetOperator k (glyzFrozenDirectionalCurve k Φ v w) t).det =
      (timeJetParameterMatrix Φ (k + 1) v t w).det := by
  change LinearMap.det (glyzCurveFullJetOperator k (glyzFrozenDirectionalCurve k Φ v w) t).toLinearMap = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis]
  have he : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis
      (glyzCurveFullJetOperator k (glyzFrozenDirectionalCurve k Φ v w) t).toLinearMap =
      (timeJetParameterMatrix Φ (k + 1) v t w).transpose := by
    ext i j
    simp only [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe, Matrix.transpose_apply]
    change (glyzCurveFullJetOperator k (glyzFrozenDirectionalCurve k Φ v w) t
      (EuclideanSpace.basisFun (Fin (k + 1)) ℝ j)) i = _
    rw [glyzCurveFullJetOperator_basis]
    exact glyzFrozenDirectionalCurve_jet_entry k Φ hΦ v w t j i
  rw [he, Matrix.det_transpose]

end PlanarNikodym
