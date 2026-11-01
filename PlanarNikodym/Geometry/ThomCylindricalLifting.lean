import PlanarNikodym.Geometry.ThomCylindricalCellUniqueness

/-! Strict sign conditions of a derivative-closed polynomial family select a
single moving root graph or adjacent band. The result uses sign invariance
already proved for the concrete graph/band construction, and does not infer
connectedness from a finite union of connected cells. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

theorem exists_analyticCylindricalCell_fiber_point {E : Type*} {n : ℕ} {C : Set E}
    (c : Fin (n + 2) → E → ℝ) (hc : ∀ x ∈ C, StrictMono (fun i => c i x))
    {x : E} (hx : x ∈ C) (i : Fin n ⊕ Fin (n + 1)) :
    ∃ t : ℝ, (x, t) ∈ analyticCylindricalCell C c i := by
  rcases i with i | i
  · exact ⟨c i.castSucc.succ x, hx, rfl⟩
  · have hlt : c i.castSucc x < c i.succ x := hc x hx (by change (i : ℕ) < (i : ℕ) + 1; omega)
    exact ⟨(c i.castSucc x + c i.succ x) / 2, hx, by linarith, by linarith⟩

def polynomialCylindricalSignCell {E ι : Type*} (C : Set E) (A B : ℝ)
    (P : E → ι → ℝ[X]) (s : ι → Fin 3) : Set (E × ℝ) :=
  {z | z ∈ C ×ˢ Ioo A B ∧ ∀ q, oneDimensionalSign ((P z.1 q).eval z.2) = s q}

/-- If actual root graphs/bands are sign invariant, complete derivative
signs identify one cell, rather than an arbitrary finite union of cells. -/
theorem polynomialCylindricalSignCell_eq_cell_or_empty
    {E ι : Type*} [Fintype ι] {n : ℕ} (C : Set E) (A B : ℝ)
    (P : E → ι → ℝ[X]) (ρ : Fin n → E → ℝ)
    (hc : ∀ x ∈ C, StrictMono (fun i => analyticRootCuts A B ρ i x))
    (hder : ∀ x ∈ C, ∀ q, ∃ r, (P x q).derivative = P x r)
    (hroot : ∀ x ∈ C, ∀ l : Fin n, ∃ q, P x q ≠ 0 ∧ (P x q).eval (ρ l x) = 0)
    (hsign : ∀ i q z, z ∈ analyticCylindricalCell C (analyticRootCuts A B ρ) i →
      ∀ w, w ∈ analyticCylindricalCell C (analyticRootCuts A B ρ) i →
        oneDimensionalSign ((P z.1 q).eval z.2) = oneDimensionalSign ((P w.1 q).eval w.2))
    (s : ι → Fin 3) :
    polynomialCylindricalSignCell C A B P s = ∅ ∨
      ∃ i, polynomialCylindricalSignCell C A B P s =
        analyticCylindricalCell C (analyticRootCuts A B ρ) i := by
  classical
  let c := analyticRootCuts A B ρ
  have hcover : (⋃ i, analyticCylindricalCell C c i) = C ×ˢ Ioo A B := by
    rw [iUnion_analyticCylindricalCell c hc]
    simp only [c, analyticRootCuts_zero, analyticRootCuts_last]
    rfl
  rcases Set.eq_empty_or_nonempty (polynomialCylindricalSignCell C A B P s) with hempty | hne
  · exact Or.inl hempty
  · right
    obtain ⟨a, ha⟩ := hne
    have haCover : a ∈ ⋃ i, analyticCylindricalCell C c i := by rw [hcover]; exact ha.1
    obtain ⟨i, hai⟩ := mem_iUnion.mp haCover
    refine ⟨i, Set.Subset.antisymm ?_ ?_⟩
    · intro z hz
      have hzCover : z ∈ ⋃ i, analyticCylindricalCell C c i := by rw [hcover]; exact hz.1
      obtain ⟨j, hzj⟩ := mem_iUnion.mp hzCover
      obtain ⟨t, htj⟩ := exists_analyticCylindricalCell_fiber_point c hc ha.1.1 j
      have hts : t ∈ polynomialThomFamilyCell false (P a.1) s := by
        intro q
        exact (hsign j q (a.1, t) htj z hzj).trans (hz.2 q)
      have hai' : a.2 ∈ orderedRealCutCell (fun k => c k a.1) i := by cases i <;> exact hai.2
      have htj' : t ∈ orderedRealCutCell (fun k => c k a.1) j := by cases j <;> exact htj.2
      have hroot' (l : Fin n) : ∃ q, P a.1 q ≠ 0 ∧
          (P a.1 q).eval (c l.castSucc.succ a.1) = 0 := by
        simpa only [c, analyticRootCuts_interior] using hroot a.1 ha.1.1 l
      have hij := polynomialThomFamilyCell_cut_index_unique (P a.1) (hder a.1 ha.1.1)
        (fun k => c k a.1) (hc a.1 ha.1.1) hroot' s hai' htj' ha.2 hts
      exact hij.symm ▸ hzj
    · intro z hz
      have hzin : z ∈ C ×ˢ Ioo A B := by
        rw [← hcover]
        exact mem_iUnion.mpr ⟨i, hz⟩
      exact ⟨hzin, fun q => (hsign i q z hz a hai).trans (ha.2 q)⟩

end PlanarNikodym
