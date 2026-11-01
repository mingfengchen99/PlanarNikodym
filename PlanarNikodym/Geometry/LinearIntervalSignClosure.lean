import PlanarNikodym.Geometry.PolynomialThomSigns
import PlanarNikodym.Geometry.FiniteIntervalDensity

/-! Exact weak-sign closure for finitely many linear cuts inside a bounded
interval. Empty strict cells are excluded explicitly. -/
noncomputable section
open Set Metric
namespace PlanarNikodym

def linearIntervalSignCell (weak : Bool) (I : Interval) (S : Finset ℝ)
    (τ : S → Fin 3) : Set ℝ :=
  {x | (if weak then x ∈ Icc I.left I.right else x ∈ Ioo I.left I.right) ∧
    ∀ z : S, polynomialSignCondition weak (τ z) (x - z)}

theorem linearIntervalSignCell_ordConnected (weak : Bool) (I : Interval) (S : Finset ℝ)
    (τ : S → Fin 3) : (linearIntervalSignCell weak I S τ).OrdConnected := by
  refine ⟨?_⟩
  intro x hx y hy t ht
  refine ⟨?_, ?_⟩
  · cases weak
    · exact ⟨hx.1.1.trans_le ht.1, ht.2.trans_lt hy.1.2⟩
    · exact ⟨hx.1.1.trans ht.1, ht.2.trans hy.1.2⟩
  · intro z
    exact (polynomialSignCondition_ordConnected weak (τ z)).out (hx.2 z) (hy.2 z)
      ⟨sub_le_sub_right ht.1 _, sub_le_sub_right ht.2 _⟩

theorem isClosed_linearIntervalWeakSignCell (I : Interval) (S : Finset ℝ)
    (τ : S → Fin 3) : IsClosed (linearIntervalSignCell true I S τ) := by
  have he : linearIntervalSignCell true I S τ = Icc I.left I.right ∩ ⋂ z : S,
      (fun x => x - (z : ℝ)) ⁻¹' {r | polynomialSignCondition true (τ z) r} := by
    ext x
    simp [linearIntervalSignCell]
  rw [he]
  exact isClosed_Icc.inter (isClosed_iInter (fun z =>
    (isClosed_polynomialWeakSignCondition (τ z)).preimage (continuous_id.sub continuous_const)))

theorem linearIntervalSignCell_subset_weak (I : Interval) (S : Finset ℝ)
    (τ : S → Fin 3) : linearIntervalSignCell false I S τ ⊆ linearIntervalSignCell true I S τ := by
  intro x hx
  exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, fun z => polynomialSignCondition_weaken (hx.2 z)⟩

/-- Every nonempty linear-cut cell has exactly its weak-sign cell as its
ambient real-line closure, including singleton cells and interval endpoints. -/
theorem linearIntervalSignCell_closure (I : Interval) (S : Finset ℝ)
    (τ : S → Fin 3) (hne : (linearIntervalSignCell false I S τ).Nonempty) :
    closure (linearIntervalSignCell false I S τ) = linearIntervalSignCell true I S τ := by
  classical
  let F : Set ℝ := {I.left, I.right} ∪ {x | ∃ z : S, τ z ≠ 1 ∧ x = z}
  have hF : F.Finite := ((Set.finite_singleton I.right).insert I.left).union
    ((Finset.finite_toSet S).subset (fun x hx => by
      obtain ⟨z, _, rfl⟩ := hx
      exact z.property))
  have he : linearIntervalSignCell false I S τ = linearIntervalSignCell true I S τ \ F := by
    ext x
    constructor
    · intro hx
      refine ⟨linearIntervalSignCell_subset_weak I S τ hx, ?_⟩
      intro hxF
      rcases hxF with hxAB | ⟨z, hz, hxz⟩
      · simp only [mem_insert_iff, mem_singleton_iff] at hxAB
        rcases hxAB with rfl | rfl
        · exact lt_irrefl _ hx.1.1
        · exact lt_irrefl _ hx.1.2
      · exact polynomialSignCondition_ne_zero hz (hx.2 z) (sub_eq_zero.mpr hxz)
    · rintro ⟨hw, hn⟩
      have hxA : x ≠ I.left := fun h => hn (Or.inl (Or.inl h))
      have hxB : x ≠ I.right := fun h => hn (Or.inl (Or.inr (mem_singleton_iff.mpr h)))
      refine ⟨⟨lt_of_le_of_ne hw.1.1 (Ne.symm hxA), lt_of_le_of_ne hw.1.2 hxB⟩, ?_⟩
      intro z
      apply polynomialSignCondition_strict_of_weak (hw.2 z)
      intro hz heq
      exact hn (Or.inr ⟨z, hz, sub_eq_zero.mp heq⟩)
  apply Subset.antisymm
  · exact closure_minimal (linearIntervalSignCell_subset_weak I S τ)
      (isClosed_linearIntervalWeakSignCell I S τ)
  · rw [he]
    exact ordConnected_subset_closure_sdiff_finite
      (linearIntervalSignCell_ordConnected true I S τ) hF (he ▸ hne)

end PlanarNikodym
