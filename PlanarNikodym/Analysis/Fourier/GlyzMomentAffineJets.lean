import PlanarNikodym.Analysis.Fourier.GlyzMomentAffine
import PlanarNikodym.Analysis.Fourier.GlyzProjectedCurve

/-! The concrete binomial affine map transports the actual derivatives
of Gamma, not only its sampled values. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace PlanarNikodym

theorem glyzMomentAffineLinear_jet (m q : ℕ) (c κ s : ℝ) (hκ : κ ≠ 0) (j : Fin q) :
    glyzMomentAffineLinear m c κ hκ (glyzMomentJetBlock m q s j) =
      κ ^ ((j : ℕ) + 1) • glyzMomentJetBlock m q (c + κ * s) j := by
  ext k
  let n := (j : ℕ) + 1
  have hf : (fun u : ℝ => (c + κ * u) ^ ((k : ℕ) + 1)) =
      fun u => c ^ ((k : ℕ) + 1) + glyzMomentAffineLinear m c κ hκ (glyzMomentCurve m u) k :=
    funext fun u => congrFun (glyzMomentAffineLinear_curve m c κ u hκ) k
  have hchain : iteratedDeriv n (fun u : ℝ => (c + κ * u) ^ ((k : ℕ) + 1)) s =
      κ ^ n * iteratedDeriv n (fun u : ℝ => u ^ ((k : ℕ) + 1)) (c + κ * s) := by
    have h := congrFun (iteratedDeriv_comp_const_mul (n := n)
      (f := fun u : ℝ => (c + u) ^ ((k : ℕ) + 1)) (by fun_prop) κ) s
    have hs := iteratedDeriv_comp_const_add (n := n) (f := fun u : ℝ => u ^ ((k : ℕ) + 1)) (s := c)
    rw [hs] at h
    exact h
  change glyzMomentAffineLinear m c κ hκ
    (fun k => iteratedDeriv n (fun u : ℝ => u ^ ((k : ℕ) + 1)) s) k = _
  calc
    _ = iteratedDeriv n (fun u => glyzMomentAffineLinear m c κ hκ (glyzMomentCurve m u) k) s :=
      (iteratedDeriv_glyzMomentCurve_linear
        ((ContinuousLinearMap.proj k : Base m →L[ℝ] ℝ).comp
          (glyzMomentAffineLinear m c κ hκ).toContinuousLinearMap) n s).symm
    _ = iteratedDeriv n (fun u : ℝ => (c + κ * u) ^ ((k : ℕ) + 1)) s := by
      rw [hf, iteratedDeriv_const_add (show 0 < n by omega)]
    _ = _ := hchain

def glyzMomentAffineEuclidean (m : ℕ) (c κ : ℝ) (hκ : κ ≠ 0) :
    GlyzSpace m ≃L[ℝ] GlyzSpace m :=
  ((EuclideanSpace.equiv (Fin m) ℝ).trans (glyzMomentAffineLinear m c κ hκ)).trans
    (EuclideanSpace.equiv (Fin m) ℝ).symm

theorem glyzMomentAffineEuclidean_jet (m q : ℕ) (c κ s : ℝ) (hκ : κ ≠ 0) (j : Fin q) :
    glyzMomentAffineEuclidean m c κ hκ (glyzEuclideanJetBlock m q s j) =
      κ ^ ((j : ℕ) + 1) • glyzEuclideanJetBlock m q (c + κ * s) j := by
  simp only [glyzMomentAffineEuclidean, glyzEuclideanJetBlock, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, glyzMomentAffineLinear_jet, map_smul]

theorem glyzMomentAffineEuclidean_curve (m : ℕ) (c κ s : ℝ) (hκ : κ ≠ 0) :
    (EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m (c + κ * s)) =
      (EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m c) +
        glyzMomentAffineEuclidean m c κ hκ
          ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m s)) := by
  rw [glyzMomentAffineLinear_curve m c κ s hκ, map_add]
  rfl

end PlanarNikodym
