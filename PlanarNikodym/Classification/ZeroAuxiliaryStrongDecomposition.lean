import PlanarNikodym.Cells.ZeroAuxiliaryFiniteRankDecomposition
import PlanarNikodym.Geometry.AnalyticFamilyNeighborhood
import PlanarNikodym.Tame.SemianalyticParameterSeeds
import PlanarNikodym.Cells.DecompositionClassification
import PlanarNikodym.Classification.AnalyticCountableConsequences

/-! The strong legacy finite-decomposition conclusion is actually proved
for every zero-auxiliary analytic parameter seed. The original domain is
covered, the retained images are disjoint, and the exception is closed and
null. This is stronger than choosing a finite classification witness. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem Family.exists_zero_auxiliary_finite_rankDecomposition
    (G : Family 2 0) (hb : Bornology.IsBounded G.W)
    (ha : G.IsAnalyticAtClosure)
    (hS : LocallySemianalytic ((parameterFrame 0) ⁻¹' G.W)) :
    Nonempty (RankDecomposition G) := by
  let e := parameterFrame 0
  let S := e ⁻¹' G.W
  let H := G.restrictTo G.analyticParameterNeighborhood
  have hHo : IsOpen H.W := G.isOpen_analyticParameterNeighborhood
  have hHa : H.IsAnalytic := G.isAnalytic_on_analyticParameterNeighborhood
  have hbS : Bornology.IsBounded S := by
    rw [show S = e.symm '' G.W from (e.toEquiv.image_symm_eq_preimage G.W).symm]
    exact e.symm.lipschitz.isBounded_image hb
  have hSW : closure S ⊆ e ⁻¹' H.W := by
    rw [show closure S = e ⁻¹' closure G.W from
      (e.toHomeomorph.preimage_closure G.W).symm]
    intro x hx
    exact G.closure_subset_analyticParameterNeighborhood ha hx
  have he : H.restrictTo (e '' S) = G := by
    have hset : e '' S = G.W := e.toEquiv.image_preimage G.W
    change { G with W := e '' S } = G
    rw [hset]
  rw [← he]
  exact H.exists_zero_auxiliary_finite_rankDecomposition_on_source hHo hHa S hS hbS hSW

theorem Family.exists_zero_auxiliary_finite_rankDecomposition_seed
    (G : Family 2 0) (hD : AnalyticParameterDomain G) (ha : G.IsAnalyticAtClosure) :
    Nonempty (RankDecomposition G) :=
  G.exists_zero_auxiliary_finite_rankDecomposition hD.2.1 ha
    (G.analyticParameterDomain_semianalytic hD)

theorem proposition_1_6_strong_zero_auxiliary_proved
    (G : Family 2 0) (hD : AnalyticParameterDomain G) (ha : G.IsAnalyticAtClosure) :
    ∃ D : RankDecomposition G, D.Proposition16Conclusions := by
  obtain ⟨D⟩ := G.exists_zero_auxiliary_finite_rankDecomposition_seed hD ha
  exact ⟨D, D.proposition_1_6_of_decomposition p5_inputs_proved ha.isAnalytic⟩

end PlanarNikodym
