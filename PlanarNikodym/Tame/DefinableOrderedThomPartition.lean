import PlanarNikodym.Tame.DefinableThomRoots
import PlanarNikodym.Geometry.FiniteOrderedThomRoots

/-! Complete finite definable parameter partitions with ordered continuous
roots. This does not assert quantifier elimination, semianalytic descriptions
on one common neighborhood, or connectedness of the base pieces. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

theorem ranDefinable_polynomialThomBaseCell {ι : Type*} [Finite ι]
    {m : ℕ} (a : (ι → ℝ) → Fin m → ℝ) {U : Set (ι → ℝ)}
    (hU : RanDefinable U) (ha : ∀ j, RanDefinableOn (fun x => a x j) U)
    (i : PolynomialOrderedThomIndex m) : RanDefinable (polynomialThomBaseCell a U i) := by
  let n := i.1.val
  let D : Set (ι → ℝ) := {x | x ∈ U ∧ polynomialRealRootCount (a x) = n}
  have hD : RanDefinable D := ranDefinable_polynomialRealRootCount hU ha n
  have hcoeff (j : Fin m) : RanDefinableOn (fun x => a x j) D :=
    (ha j).restrict hD (fun _ hx => hx.1)
  have hroot (j : Fin n) :
      RanDefinableOn (fun x => orderedPolynomialRealRoot (a x) n j) D :=
    ranDefinableOn_orderedPolynomialRootBranch hD hcoeff
      (fun x => orderedPolynomialRealRoot (a x) n)
      (fun x hx => orderedPolynomialRealRoot_spec (a x) n hx.2) j
  have hsign (j : Fin n) (k : Fin (m + 1)) :
      RanDefinable {x | x ∈ D ∧
        oneDimensionalSign ((derivative^[k.val] (weierstrassPolynomial (a x))).eval
          (orderedPolynomialRealRoot (a x) n j)) = i.2 j k} :=
    ranDefinableOn_oneDimensionalSign_eq hD
      (ranDefinableOn_weierstrassPolynomial_iterate_derivative_eval hD hcoeff (hroot j) k.val) _
  convert hD.inter (Set.definable_iInter_of_finite
    (fun j => Set.definable_iInter_of_finite (hsign j))) using 1
  ext x
  simp only [polynomialThomBaseCell, mem_setOf_eq, polynomialOrderedThomIndex_eq_iff,
    mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hx, hn, hc⟩
    exact ⟨⟨hx, hn⟩, fun j k => ⟨⟨hx, hn⟩, congrFun (hc j) k⟩⟩
  · rintro ⟨⟨hx, hn⟩, hc⟩
    exact ⟨hx, hn, fun j => funext (fun k => (hc j k).2)⟩

theorem ranDefinableOn_polynomialThomBaseCell_root {ι : Type*} [Finite ι]
    {m : ℕ} (a : (ι → ℝ) → Fin m → ℝ) {U : Set (ι → ℝ)}
    (hU : RanDefinable U) (ha : ∀ j, RanDefinableOn (fun x => a x j) U)
    (i : PolynomialOrderedThomIndex m) (k : Fin i.1.val) :
    RanDefinableOn (polynomialThomRoot a (i.2 k)) (polynomialThomBaseCell a U i) :=
  (ranDefinableOn_polynomialThomRoot hU ha (i.2 k)).restrict
    (ranDefinable_polynomialThomBaseCell a hU ha i)
    (fun _ hx => ⟨hx.1, polynomialThomBaseCell_mem_domain a U i k hx⟩)

/-- Actual finite partition and root construction, with no discriminant or
constant multiplicity hypothesis. Base cells and complete ordered roots are
definable; coefficients need only be continuous on their original open domain. -/
theorem finite_continuous_definable_polynomial_root_partition
    {ι : Type*} [Fintype ι] {m : ℕ} (a : (ι → ℝ) → Fin m → ℝ)
    (U : Set (ι → ℝ)) (ho : IsOpen U) (hU : RanDefinable U)
    (ha : ContinuousOn a U) (hda : ∀ j, RanDefinableOn (fun x => a x j) U) :
    (⋃ i : PolynomialOrderedThomIndex m, polynomialThomBaseCell a U i) = U ∧
    Pairwise (fun i j : PolynomialOrderedThomIndex m =>
      Disjoint (polynomialThomBaseCell a U i) (polynomialThomBaseCell a U j)) ∧
    ∀ i : PolynomialOrderedThomIndex m,
      RanDefinable (polynomialThomBaseCell a U i) ∧
      (∀ k, ContinuousOn (polynomialThomRoot a (i.2 k)) (polynomialThomBaseCell a U i)) ∧
      (∀ k, RanDefinableOn (polynomialThomRoot a (i.2 k)) (polynomialThomBaseCell a U i)) ∧
      ∀ x ∈ polynomialThomBaseCell a U i,
        StrictMono (fun k => polynomialThomRoot a (i.2 k) x) ∧
        ∀ t : ℝ, (weierstrassPolynomial (a x)).eval t = 0 ↔
          ∃ k, t = polynomialThomRoot a (i.2 k) x := by
  refine ⟨polynomialThomBaseCell_cover a U, polynomialThomBaseCell_pairwiseDisjoint a U,
    fun i => ⟨ranDefinable_polynomialThomBaseCell a hU hda i,
      continuousOn_polynomialThomBaseCell_roots a U ho ha i,
      ranDefinableOn_polynomialThomBaseCell_root a hU hda i, ?_⟩⟩
  exact fun _ hx => polynomialThomBaseCell_ordered_roots a U i hx

end PlanarNikodym
