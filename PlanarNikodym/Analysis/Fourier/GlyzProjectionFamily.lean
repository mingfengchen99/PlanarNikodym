import PlanarNikodym.Analysis.Fourier.GlyzContinuousProjection

/-! The actual tangent-frame family and ambient orthogonal projections
of the moment curve vary continuously with the center. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Submodule
open scoped BigOperators
namespace PlanarNikodym

theorem continuous_glyzEuclideanJetBlock (m q : ℕ) (j : Fin q) :
    Continuous (fun s => glyzEuclideanJetBlock m q s j) := by
  apply (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp
  apply continuous_pi
  intro k
  simp only [glyzMomentJetBlock, glyzMomentCurve, iteratedDeriv_pow]
  fun_prop

def glyzTangentFrame (l r : ℕ) (t : ℝ) : GlyzSpace r →L[ℝ] GlyzSpace (l + r) :=
  ∑ j : Fin r, (((ContinuousLinearMap.proj j : Base r →L[ℝ] ℝ).comp
    (EuclideanSpace.equiv (Fin r) ℝ).toContinuousLinearMap).smulRight
      (glyzEuclideanJetBlock (l + r) r t j))

theorem glyzTangentFrame_apply (l r : ℕ) (t : ℝ) (v : GlyzSpace r) :
    glyzTangentFrame l r t v = ∑ j : Fin r, v j • glyzEuclideanJetBlock (l + r) r t j := by
  simp only [glyzTangentFrame, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply]
  rfl

theorem glyzTangentFrame_basis (l r : ℕ) (t : ℝ) (j : Fin r) :
    glyzTangentFrame l r t (EuclideanSpace.basisFun (Fin r) ℝ j) =
      glyzEuclideanJetBlock (l + r) r t j := by
  rw [glyzTangentFrame_apply]
  simp [EuclideanSpace.basisFun_apply]

theorem range_glyzTangentFrame (l r : ℕ) (t : ℝ) :
    (glyzTangentFrame l r t).range = glyzEuclideanTangentSpace (l + r) r t := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    change glyzTangentFrame l r t v ∈ glyzEuclideanTangentSpace (l + r) r t
    rw [glyzTangentFrame_apply]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨EuclideanSpace.basisFun (Fin r) ℝ j, glyzTangentFrame_basis l r t j⟩

theorem injective_glyzTangentFrame (l r : ℕ) (t : ℝ) :
    Function.Injective (glyzTangentFrame l r t) := by
  have h : LinearIndependent ℝ (glyzEuclideanJetBlock (l + r) r t) := by
    simpa only [Function.comp_def, Sum.elim_inr] using
      (linearIndependent_sum.mp (linearIndependent_glyzEuclideanMixedJets l r
        (s := t + 1) (t := t) (by linarith))).2.1
  intro v w hvw
  apply (EuclideanSpace.equiv (Fin r) ℝ).injective
  apply h.fintypeLinearCombination_injective
  change (∑ j : Fin r, v j • glyzEuclideanJetBlock (l + r) r t j) =
    ∑ j : Fin r, w j • glyzEuclideanJetBlock (l + r) r t j
  simpa only [glyzTangentFrame_apply] using hvw

theorem continuous_glyzTangentFrame (l r : ℕ) : Continuous (glyzTangentFrame l r) := by
  apply continuous_finsetSum
  intro j _
  exact (ContinuousLinearMap.smulRightL ℝ (GlyzSpace r) (GlyzSpace (l + r)) _).continuous.comp
    (continuous_glyzEuclideanJetBlock (l + r) r j)

def glyzOrthogonalOperator (l r : ℕ) (t : ℝ) : GlyzSpace (l + r) →L[ℝ] GlyzSpace (l + r) :=
  (glyzEuclideanTangentSpace (l + r) r t)ᗮ.starProjection

theorem continuous_glyzOrthogonalOperator (l r : ℕ) : Continuous (glyzOrthogonalOperator l r) := by
  have hc := glyz_continuous_range_starProjection (glyzTangentFrame l r)
    (continuous_glyzTangentFrame l r) (injective_glyzTangentFrame l r)
  simp only [range_glyzTangentFrame] at hc
  have he : glyzOrthogonalOperator l r = fun t =>
      (1 : GlyzSpace (l + r) →L[ℝ] GlyzSpace (l + r)) -
        (glyzEuclideanTangentSpace (l + r) r t).starProjection :=
    funext fun t => Submodule.starProjection_orthogonal _
  rw [he]
  exact continuous_const.sub hc

theorem continuous_glyzAmbientProjectedJets (l r : ℕ) (j : Fin l) :
    Continuous (fun z : ℝ × ℝ => glyzOrthogonalOperator l r z.2
      (glyzEuclideanJetBlock (l + r) l z.1 j)) :=
  ((continuous_glyzOrthogonalOperator l r).comp continuous_snd).clm_apply
    ((continuous_glyzEuclideanJetBlock (l + r) l j).comp continuous_fst)

end PlanarNikodym
