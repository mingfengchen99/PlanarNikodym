import PlanarNikodym.Geometry.AnalyticStratificationChartTopology
import PlanarNikodym.Core.Definitions
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! Actual linear coordinates adapted to a surjective centre derivative.
The right inverse, kernel coordinates and continuous linear equivalence
are constructed from surjectivity. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem exists_center_derivative_coordinates {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] Base 2) (hL : Function.Surjective L) :
    ∃ (k : ℕ) (e : Parameters 2 k ≃L[ℝ] (Fin n → ℝ)),
      k + 2 = n ∧ ∀ z, L (e z) = z.1 := by
  classical
  let K := LinearMap.ker L.toLinearMap
  let S : Base 2 →L[ℝ] (Fin n → ℝ) :=
    (L.toLinearMap.splittingOfFunOnFintypeSurjective hL).toContinuousLinearMap
  have hS (z : Base 2) : L (S z) = z :=
    LinearMap.leftInverse_splittingOfFunOnFintypeSurjective L.toLinearMap hL z
  let T : (Base 2 × K) →L[ℝ] (Fin n → ℝ) := S.coprod K.subtypeL
  have hT (z : Base 2 × K) : L (T z) = z.1 := by
    change L (S z.1 + z.2.val) = z.1
    rw [map_add, hS]
    have hz : L z.2.val = 0 := z.2.property
    rw [hz, add_zero]
  have hTi : Function.Injective T := by
    intro z w hzw
    have hfst : z.1 = w.1 := (hT z).symm.trans ((congrArg L hzw).trans (hT w))
    apply Prod.ext hfst
    apply Subtype.ext
    change S z.1 + z.2.val = S w.1 + w.2.val at hzw
    rw [hfst] at hzw
    exact add_left_cancel hzw
  have hTs : Function.Surjective T := by
    intro x
    have hx : x - S (L x) ∈ K := by
      change L (x - S (L x)) = 0
      rw [map_sub, hS, sub_self]
    refine ⟨(L x, ⟨x - S (L x), hx⟩), ?_⟩
    change S (L x) + (x - S (L x)) = x
    abel
  let e₀ : (Base 2 × K) ≃L[ℝ] (Fin n → ℝ) :=
    (LinearEquiv.ofBijective T.toLinearMap ⟨hTi, hTs⟩).toContinuousLinearEquiv
  let k := Module.finrank ℝ K
  let c : (Fin k → ℝ) ≃L[ℝ] K :=
    (Module.finBasis ℝ K).equivFun.symm.toContinuousLinearEquiv
  let e : Parameters 2 k ≃L[ℝ] (Fin n → ℝ) :=
    ((ContinuousLinearEquiv.refl ℝ (Base 2)).prodCongr c).trans e₀
  refine ⟨k, e, ?_, ?_⟩
  · have hd := e.toLinearEquiv.finrank_eq
    simpa [Parameters, Base, Aux, Module.finrank_prod, add_comm] using hd
  · intro z
    exact hT (z.1, c z.2)

end PlanarNikodym
