import PlanarNikodym.Geometry.PolynomialThomLemma
import PlanarNikodym.Geometry.AnalyticCylindricalPartition

/-! A derivative-closed strict polynomial sign cell occupies at most one
ordered root graph or adjacent band. Every cut is an actual root of a
nonzero member; no assertion about signs on moving graphs is assumed. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

def orderedRealCutCell {n : ℕ} (c : Fin (n + 2) → ℝ) :
    (Fin n ⊕ Fin (n + 1)) → Set ℝ
  | Sum.inl i => {t | t = c i.castSucc.succ}
  | Sum.inr i => Ioo (c i.castSucc) (c i.succ)

theorem orderedRealCutCell_index_eq {n : ℕ} (c : Fin (n + 2) → ℝ) (hc : StrictMono c)
    {i j : Fin n ⊕ Fin (n + 1)} {t : ℝ}
    (hi : t ∈ orderedRealCutCell c i) (hj : t ∈ orderedRealCutCell c j) : i = j := by
  have hci : ((), t) ∈ analyticCylindricalCell (univ : Set Unit) (fun k _ => c k) i := by
    cases i <;> exact ⟨mem_univ _, hi⟩
  have hcj : ((), t) ∈ analyticCylindricalCell (univ : Set Unit) (fun k _ => c k) j := by
    cases j <;> exact ⟨mem_univ _, hj⟩
  exact analyticCylindricalCell_index_eq (fun _ _ => hc) hci hcj

/-- At one parameter, two points with the same complete derivative signs
belong to the same root graph/band index. -/
theorem polynomialThomFamilyCell_cut_index_unique
    {ι : Type*} [Fintype ι] {n : ℕ} (P : ι → ℝ[X])
    (hder : ∀ j, ∃ k, (P j).derivative = P k)
    (c : Fin (n + 2) → ℝ) (hc : StrictMono c)
    (hroot : ∀ l : Fin n, ∃ q, P q ≠ 0 ∧ (P q).eval (c l.castSucc.succ) = 0)
    (s : ι → Fin 3) {i j : Fin n ⊕ Fin (n + 1)} {y z : ℝ}
    (hy : y ∈ orderedRealCutCell c i) (hz : z ∈ orderedRealCutCell c j)
    (hys : y ∈ polynomialThomFamilyCell false P s)
    (hzs : z ∈ polynomialThomFamilyCell false P s) : i = j := by
  have hpoint (l : Fin n) {t : ℝ} (ht : t = c l.castSucc.succ)
      (hts : t ∈ polynomialThomFamilyCell false P s) :
      (polynomialThomFamilyCell false P s).Subsingleton := by
    obtain ⟨q, hn, hq⟩ := hroot l
    have heval : (P q).eval t = 0 := ht ▸ hq
    have hs : s q = 1 := (show oneDimensionalSign ((P q).eval t) = s q from hts q).symm.trans
      (oneDimensionalSign_eq_one.mpr heval)
    exact polynomialThomFamilyCell_subsingleton_of_nonzero_equality P hder s q hs hn
  have hbandle (i j : Fin (n + 1)) {y z : ℝ}
      (hy : y ∈ orderedRealCutCell c (Sum.inr i))
      (hz : z ∈ orderedRealCutCell c (Sum.inr j))
      (hys : y ∈ polynomialThomFamilyCell false P s)
      (hzs : z ∈ polynomialThomFamilyCell false P s) : i ≤ j := by
    by_contra hij
    have hji : j < i := lt_of_not_ge hij
    let l : Fin n := ⟨j, by have := i.isLt; change (j : ℕ) < (i : ℕ) at hji; omega⟩
    have heidx : j.succ = l.castSucc.succ := Fin.ext rfl
    have hcut : j.succ ≤ i.castSucc := by change (j : ℕ) + 1 ≤ (i : ℕ); exact hji
    have hwy : c l.castSucc.succ < y := by
      rw [← heidx]
      exact (hc.monotone hcut).trans_lt hy.1
    have hzw : z < c l.castSucc.succ := by rw [← heidx]; exact hz.2
    have hw : c l.castSucc.succ ∈ polynomialThomFamilyCell false P s :=
      (polynomialThomFamilyCell_ordConnected false P hder s).out hzs hys ⟨hzw.le, hwy.le⟩
    exact (ne_of_lt hzw) ((hpoint l rfl hw) hzs hw)
  rcases i with i | i
  · have he := hpoint i hy hys hys hzs
    exact orderedRealCutCell_index_eq c hc hy (he.symm ▸ hz)
  · rcases j with j | j
    · have he := hpoint j hz hzs hys hzs
      exact orderedRealCutCell_index_eq c hc hy (he.symm ▸ hz)
    · exact congrArg Sum.inr (le_antisymm (hbandle i j hy hz hys hzs) (hbandle j i hz hy hzs hys))

end PlanarNikodym
