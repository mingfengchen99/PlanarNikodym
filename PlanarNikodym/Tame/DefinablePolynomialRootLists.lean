import PlanarNikodym.Tame.DefinablePolynomialDivision
import PlanarNikodym.Tame.DefinableTopology
import PlanarNikodym.Tame.DefinableRankMinors

/-! Ordered complete real-root lists have actual first-order graphs. In
particular a constructed analytic root atlas does not need a separate
definability assumption on its branch functions. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

theorem ranDefinableFun_pow {ι : Type*} {f : (ι → ℝ) → ℝ}
    (hf : RanDefinableFun f) (n : ℕ) : RanDefinableFun (fun x => f x ^ n) := by
  induction n with
  | zero => simpa using ranDefinableFun_const (ι := ι) 1
  | succ n ih => simpa only [pow_succ] using ranDefinableFun_mul ih hf

theorem ranDefinableFun_weierstrassPolynomial_eval {ι : Type*} {m : ℕ}
    {a : (ι → ℝ) → Fin m → ℝ} {t : (ι → ℝ) → ℝ}
    (ha : RanDefinableMap a) (ht : RanDefinableFun t) :
    RanDefinableFun (fun x => (weierstrassPolynomial (a x)).eval (t x)) := by
  simp only [weierstrassPolynomial_eval]
  exact ranDefinableFun_add (ranDefinableFun_pow ht m)
    (ranDefinableFun_finset_sum Finset.univ (fun i _ =>
      ranDefinableFun_mul (ha i) (ranDefinableFun_pow ht i)))

def IsOrderedPolynomialRootList {m n : ℕ} (a : Fin m → ℝ) (r : Fin n → ℝ) : Prop :=
  StrictMono r ∧ ∀ t, (weierstrassPolynomial a).eval t = 0 ↔ ∃ i, t = r i

theorem IsOrderedPolynomialRootList.unique {m n : ℕ} {a : Fin m → ℝ}
    {r s : Fin n → ℝ} (hr : IsOrderedPolynomialRootList a r)
    (hs : IsOrderedPolynomialRootList a s) : r = s := by
  apply (hr.1.range_inj hs.1).mp
  ext t
  simpa only [mem_range, eq_comm] using (hr.2 t).symm.trans (hs.2 t)

theorem ranDefinable_isOrderedPolynomialRootList {ι : Type*} [Finite ι]
    {m n : ℕ} {a : (ι → ℝ) → Fin m → ℝ} {r : (ι → ℝ) → Fin n → ℝ}
    (ha : RanDefinableMap a) (hr : RanDefinableMap r) :
    RanDefinable {x | IsOrderedPolynomialRootList (a x) (r x)} := by
  classical
  have hord : RanDefinable {x | StrictMono (r x)} := by
    have hij (i j : Fin n) : RanDefinable {x | i < j → r x i < r x j} := by
      by_cases h : i < j
      · simpa only [h, true_implies] using ranDefinable_lt (hr i) (hr j)
      · simpa only [h, false_implies, setOf_true] using
          (Set.definable_univ : RanDefinable (univ : Set (ι → ℝ)))
    convert Set.definable_iInter_of_finite
      (fun i => Set.definable_iInter_of_finite (hij i)) using 1
    ext x
    simp only [mem_setOf_eq, mem_iInter, StrictMono]
  have hzero : RanDefinable {w : Option ι → ℝ |
      (weierstrassPolynomial (a (w ∘ some))).eval (w none) = 0} :=
    (ranDefinableFun_weierstrassPolynomial_eval
      (fun i => (ha i).comp (fun j => ranDefinableFun_coordinate (some j)))
      (ranDefinableFun_coordinate none)).setOf_eq (ranDefinableFun_const 0)
  have hlist : RanDefinable {w : Option ι → ℝ | ∃ i, w none = r (w ∘ some) i} := by
    convert Set.definable_iUnion_of_finite
      (fun i => (ranDefinableFun_coordinate none).setOf_eq
        ((hr i).comp (fun j => ranDefinableFun_coordinate (some j)))) using 1
    ext w
    simp only [mem_setOf_eq, mem_iUnion]
    rfl
  have hall := ranDefinable_forall_real
    (P := fun x t => (weierstrassPolynomial (a x)).eval t = 0 ↔ ∃ i, t = r x i)
    (by
      convert (hzero.inter hlist).union (hzero.compl.inter hlist.compl) using 1
      ext w
      simp only [mem_setOf_eq, mem_union, mem_inter_iff, mem_compl_iff]
      tauto)
  exact hord.inter hall

theorem ranDefinable_exists_orderedPolynomialRootList {ι : Type*} [Finite ι]
    {m : ℕ} {a : (ι → ℝ) → Fin m → ℝ} {S : Set (ι → ℝ)}
    (hS : RanDefinable S) (ha : ∀ i, RanDefinableOn (fun x => a x i) S) (n : ℕ) :
    RanDefinable {x | x ∈ S ∧ ∃ r : Fin n → ℝ, IsOrderedPolynomialRootList (a x) r} := by
  classical
  let b : (ι → ℝ) → Fin m → ℝ := fun x i => ranZeroExtension (fun y => a y i) S x
  have hb : RanDefinableMap b := fun i => (ha i).zeroExtension hS
  have hrel : RanDefinable {w : (ι ⊕ Fin n) → ℝ |
      w ∘ Sum.inl ∈ S ∧ IsOrderedPolynomialRootList (b (w ∘ Sum.inl)) (w ∘ Sum.inr)} :=
    (hS.preimage_comp Sum.inl).inter
      (ranDefinable_isOrderedPolynomialRootList
        (fun i => (hb i).comp (fun j => ranDefinableFun_coordinate (Sum.inl j)))
        (fun i => ranDefinableFun_coordinate (Sum.inr i)))
  convert hrel.exists_of_finite using 1
  ext x
  simp only [mem_setOf_eq, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  by_cases hx : x ∈ S
  · have he : b x = a x := by funext i; simp only [b, ranZeroExtension, if_pos hx]
    simp only [hx, he, true_and]
  · simp [hx]

theorem ranDefinableOn_orderedPolynomialRootBranch {ι : Type*} [Finite ι]
    {m n : ℕ} {a : (ι → ℝ) → Fin m → ℝ} {S : Set (ι → ℝ)}
    (hS : RanDefinable S) (ha : ∀ i, RanDefinableOn (fun x => a x i) S)
    (r : (ι → ℝ) → Fin n → ℝ)
    (hr : ∀ x ∈ S, IsOrderedPolynomialRootList (a x) (r x)) (i : Fin n) :
    RanDefinableOn (fun x => r x i) S := by
  classical
  let b : (ι → ℝ) → Fin m → ℝ := fun x j => ranZeroExtension (fun y => a y j) S x
  have hb : RanDefinableMap b := fun j => (ha j).zeroExtension hS
  have hrel : RanDefinable {w : (Option ι ⊕ Fin n) → ℝ |
      (fun j => w (.inl (some j))) ∈ S ∧
      IsOrderedPolynomialRootList (b (fun j => w (.inl (some j)))) (w ∘ Sum.inr) ∧
      w (.inr i) = w (.inl none)} :=
    (hS.preimage_comp (fun j => Sum.inl (some j))).inter
      ((ranDefinable_isOrderedPolynomialRootList
        (fun j => (hb j).comp (fun k => ranDefinableFun_coordinate (Sum.inl (some k))))
        (fun j => ranDefinableFun_coordinate (Sum.inr j))).inter
        ((ranDefinableFun_coordinate (Sum.inr i)).setOf_eq
          (ranDefinableFun_coordinate (Sum.inl none))))
  unfold RanDefinableOn
  convert hrel.exists_of_finite using 1
  ext w
  change (w ∘ some ∈ S ∧ r (w ∘ some) i = w none) ↔
    ∃ s : Fin n → ℝ, (w ∘ some ∈ S ∧
      IsOrderedPolynomialRootList (b (w ∘ some)) s ∧ s i = w none)
  have he (hx : w ∘ some ∈ S) : b (w ∘ some) = a (w ∘ some) := by
    funext j
    simp only [b, ranZeroExtension, if_pos hx]
  constructor
  · rintro ⟨hx, hi⟩
    exact ⟨r (w ∘ some), hx, by simpa only [he hx] using hr _ hx, hi⟩
  · rintro ⟨s, hx, hs, hi⟩
    rw [he hx] at hs
    exact ⟨hx, by rw [(hr _ hx).unique hs]; exact hi⟩

end PlanarNikodym
