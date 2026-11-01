import PlanarNikodym.Geometry.AnalyticStratificationCharts

/-! Actual subspace homeomorphisms and dimension bounds for the constructed
analytic stratum charts, together with the point and open-domain charts. -/
noncomputable section
open Set
namespace PlanarNikodym
namespace AnalyticStratificationChart
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inverse_mem_source (Q : AnalyticStratificationChart E) {y : E} (hy : y ∈ Q.image) :
    Q.inverse y ∈ Q.source := by
  obtain ⟨p, hp, rfl⟩ := hy
  rw [Q.left_inverse p hp]
  exact hp

theorem map_inverse (Q : AnalyticStratificationChart E) {y : E} (hy : y ∈ Q.image) :
    Q.map (Q.inverse y) = y := by
  obtain ⟨p, hp, rfl⟩ := hy
  rw [Q.left_inverse p hp]

def homeomorph (Q : AnalyticStratificationChart E) : Q.source ≃ₜ Q.image where
  toFun p := ⟨Q.map p, mem_image_of_mem _ p.property⟩
  invFun y := ⟨Q.inverse y, Q.inverse_mem_source y.property⟩
  left_inv p := Subtype.ext (Q.left_inverse p p.property)
  right_inv y := Subtype.ext (Q.map_inverse y.property)
  continuous_toFun := Q.analytic_map.continuousOn.restrict.subtype_mk _
  continuous_invFun := Q.continuous_inverse.restrict.subtype_mk _

theorem dim_le_finrank [FiniteDimensional ℝ E] (Q : AnalyticStratificationChart E) :
    Q.dim ≤ Module.finrank ℝ E := by
  obtain ⟨p, hp⟩ := Q.connected_source.nonempty
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := (fderiv ℝ Q.map p).toLinearMap) (Q.derivative_injective p hp)
  simpa using h

def point (x : E) : AnalyticStratificationChart E where
  dim := 0
  source := univ
  open_source := isOpen_univ
  bounded_source := by
    have he : (univ : Set (Fin 0 → ℝ)) = {0} := by
      ext p
      simp only [mem_univ, mem_singleton_iff, true_iff]
      exact Subsingleton.elim p 0
    rw [he]
    exact Bornology.isBounded_singleton
  connected_source := isConnected_univ
  map := fun _ => x
  inverse := fun _ => 0
  analytic_map := fun _ _ => analyticAt_const
  continuous_inverse := continuousOn_const
  left_inverse := fun p _ => Subsingleton.elim 0 p
  derivative_injective := fun _ _ _ _ _ => Subsingleton.elim _ _

@[simp] theorem point_dim (x : E) : (point x).dim = 0 := rfl

@[simp] theorem point_image (x : E) : (point x).image = {x} := by
  ext y
  constructor
  · rintro ⟨p, _, rfl⟩
    rfl
  · intro hy
    exact ⟨0, mem_univ _, (mem_singleton_iff.mp hy).symm⟩

def openDomain {n : ℕ} (U : Set (Fin n → ℝ))
    (hU : IsOpen U) (hb : Bornology.IsBounded U) (hc : IsConnected U) :
    AnalyticStratificationChart (Fin n → ℝ) where
  dim := n
  source := U
  open_source := hU
  bounded_source := hb
  connected_source := hc
  map := id
  inverse := id
  analytic_map := fun _ _ => analyticAt_id
  continuous_inverse := continuousOn_id
  left_inverse := fun _ _ => rfl
  derivative_injective := by
    intro x _
    rw [fderiv_id]
    exact Function.injective_id

@[simp] theorem openDomain_image {n : ℕ} (U : Set (Fin n → ℝ))
    (hU : IsOpen U) (hb : Bornology.IsBounded U) (hc : IsConnected U) :
    (openDomain U hU hb hc).image = U := image_id U

end AnalyticStratificationChart
end PlanarNikodym
