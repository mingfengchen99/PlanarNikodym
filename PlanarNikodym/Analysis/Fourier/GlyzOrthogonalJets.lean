import PlanarNikodym.Analysis.Fourier.GlyzMomentBoxes
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! Actual orthogonal, rather than quotient, projection of the moment
jets used in lower-dimensional decoupling. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Submodule Module
namespace PlanarNikodym

def glyzEuclideanJetBlock (m q : ℕ) (s : ℝ) (j : Fin q) : GlyzSpace m :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentJetBlock m q s j)

def glyzEuclideanTangentSpace (m q : ℕ) (s : ℝ) : Submodule ℝ (GlyzSpace m) :=
  span ℝ (Set.range (glyzEuclideanJetBlock m q s))

theorem linearIndependent_glyzEuclideanMixedJets (l r : ℕ) {s t : ℝ} (hst : s ≠ t) :
    LinearIndependent ℝ (Sum.elim (glyzEuclideanJetBlock (l + r) l s)
      (glyzEuclideanJetBlock (l + r) r t)) := by
  have h := (linearIndependent_glyzMixedMomentJets l r hst).map'
    (EuclideanSpace.equiv (Fin (l + r)) ℝ).symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr (EuclideanSpace.equiv (Fin (l + r)) ℝ).symm.injective)
  have he : (EuclideanSpace.equiv (Fin (l + r)) ℝ).symm.toLinearMap ∘
      Sum.elim (glyzMomentJetBlock (l + r) l s) (glyzMomentJetBlock (l + r) r t) =
      Sum.elim (glyzEuclideanJetBlock (l + r) l s) (glyzEuclideanJetBlock (l + r) r t) := by
    funext j
    cases j <;> rfl
  rwa [he] at h

def glyzOrthogonalJetBlock (l r : ℕ) (s t : ℝ) (j : Fin l) :
    (glyzEuclideanTangentSpace (l + r) r t)ᗮ :=
  (glyzEuclideanTangentSpace (l + r) r t)ᗮ.orthogonalProjectionOnto
    (glyzEuclideanJetBlock (l + r) l s j)

theorem linearIndependent_glyzOrthogonalJets (l r : ℕ) {s t : ℝ} (hst : s ≠ t) :
    LinearIndependent ℝ (glyzOrthogonalJetBlock l r s t) := by
  have h := linearIndependent_sum.mp (linearIndependent_glyzEuclideanMixedJets l r hst)
  let P : GlyzSpace (l + r) →L[ℝ] (glyzEuclideanTangentSpace (l + r) r t)ᗮ :=
    (glyzEuclideanTangentSpace (l + r) r t)ᗮ.orthogonalProjectionOnto
  change LinearIndependent ℝ (P.toLinearMap ∘ glyzEuclideanJetBlock (l + r) l s)
  apply (P.toLinearMap.linearIndependent_iff_of_disjoint ?_).mpr
    (by simpa only [Function.comp_def, Sum.elim_inl] using h.1)
  change Disjoint (span ℝ (Set.range (glyzEuclideanJetBlock (l + r) l s)))
    ((glyzEuclideanTangentSpace (l + r) r t)ᗮ.orthogonalProjectionOnto.ker)
  rw [Submodule.ker_orthogonalProjectionOnto, Submodule.orthogonal_orthogonal]
  simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, glyzEuclideanTangentSpace] using h.2.2

theorem finrank_glyzEuclideanTangentSpace (l r : ℕ) (t : ℝ) :
    finrank ℝ (glyzEuclideanTangentSpace (l + r) r t) = r := by
  have h := (linearIndependent_sum.mp
    (linearIndependent_glyzEuclideanMixedJets l r (s := t + 1) (t := t) (by linarith))).2.1
  simpa only [glyzEuclideanTangentSpace, Fintype.card_fin, Function.comp_def, Sum.elim_inr] using finrank_span_eq_card h

theorem finrank_glyzOrthogonalSpace (l r : ℕ) (t : ℝ) :
    finrank ℝ (glyzEuclideanTangentSpace (l + r) r t)ᗮ = l := by
  have h := (glyzEuclideanTangentSpace (l + r) r t).finrank_add_finrank_orthogonal
  rw [finrank_glyzEuclideanTangentSpace, finrank_euclideanSpace, Fintype.card_fin] at h
  omega

theorem det_gram_glyzOrthogonalJets_ne_zero (l r : ℕ) {s t : ℝ} (hst : s ≠ t) :
    (Matrix.gram ℝ (glyzOrthogonalJetBlock l r s t)).det ≠ 0 :=
  Matrix.det_gram_ne_zero_iff_linearIndependent.mpr (linearIndependent_glyzOrthogonalJets l r hst)

end PlanarNikodym
