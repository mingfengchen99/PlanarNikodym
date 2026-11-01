import PlanarNikodym.Geometry.ContinuousThomRoots
import PlanarNikodym.Tame.DefinablePolynomialRootDomains

/-! Actual first-order graphs for Thom occurrence loci and their canonical
roots. The coefficient graphs are needed only on the original domain. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

theorem ranDefinableFun_weierstrassPolynomial_coeff {ι : Type*}
    {m : ℕ} {a : (ι → ℝ) → Fin m → ℝ} (ha : RanDefinableMap a) (k : ℕ) :
    RanDefinableFun (fun x => (weierstrassPolynomial (a x)).coeff k) := by
  have h := (ranDefinableOn_weierstrassPolynomial_coeff Set.definable_univ
    (fun i => RanDefinableFun.ranDefinableOn (ha i) Set.definable_univ) k).zeroExtension Set.definable_univ
  have he : ranZeroExtension (fun x => (weierstrassPolynomial (a x)).coeff k) univ =
      (fun x => (weierstrassPolynomial (a x)).coeff k) := by
    funext x
    simp [ranZeroExtension]
  rw [he] at h
  exact h

theorem ranDefinableFun_weierstrassPolynomial_iterate_derivative_eval
    {ι : Type*} {m : ℕ} {a : (ι → ℝ) → Fin m → ℝ} {t : (ι → ℝ) → ℝ}
    (ha : RanDefinableMap a) (ht : RanDefinableFun t) (k : ℕ) :
    RanDefinableFun (fun x => (derivative^[k] (weierstrassPolynomial (a x))).eval (t x)) := by
  have hd (x : ι → ℝ) : (derivative^[k] (weierstrassPolynomial (a x))).natDegree < m + 1 := by
    have h := natDegree_iterate_derivative (weierstrassPolynomial (a x)) k
    rw [weierstrassPolynomial_natDegree] at h
    omega
  have he (x : ι → ℝ) :
      (derivative^[k] (weierstrassPolynomial (a x))).eval (t x) =
        ∑ i ∈ Finset.range (m + 1),
          ((i + k).descFactorial k : ℝ) * (weierstrassPolynomial (a x)).coeff (i + k) * t x ^ i := by
    rw [eval_eq_sum_range' (hd x)]
    simp only [coeff_iterate_derivative, nsmul_eq_mul]
  simp_rw [he]
  exact ranDefinableFun_finset_sum _ (fun i _ =>
    ranDefinableFun_mul
      (ranDefinableFun_mul (ranDefinableFun_const _)
        (ranDefinableFun_weierstrassPolynomial_coeff ha (i + k)))
      (ranDefinableFun_pow ht i))

theorem ranDefinable_oneDimensionalSign_eq {ι : Type*} {f : (ι → ℝ) → ℝ}
    (hf : RanDefinableFun f) (s : Fin 3) : RanDefinable {x | oneDimensionalSign (f x) = s} := by
  fin_cases s
  · change RanDefinable {x | oneDimensionalSign (f x) = 0}
    simpa only [oneDimensionalSign_eq_zero] using ranDefinable_lt hf (ranDefinableFun_const 0)
  · change RanDefinable {x | oneDimensionalSign (f x) = 1}
    simpa only [oneDimensionalSign_eq_one] using hf.setOf_eq (ranDefinableFun_const 0)
  · change RanDefinable {x | oneDimensionalSign (f x) = 2}
    simpa only [oneDimensionalSign_eq_two] using ranDefinable_lt (ranDefinableFun_const 0) hf

theorem ranDefinableOn_weierstrassPolynomial_iterate_derivative_eval
    {ι : Type*} {m : ℕ} {a : (ι → ℝ) → Fin m → ℝ} {t : (ι → ℝ) → ℝ}
    {S : Set (ι → ℝ)} (hS : RanDefinable S)
    (ha : ∀ j, RanDefinableOn (fun x => a x j) S) (ht : RanDefinableOn t S) (k : ℕ) :
    RanDefinableOn (fun x => (derivative^[k] (weierstrassPolynomial (a x))).eval (t x)) S := by
  classical
  let b : (ι → ℝ) → Fin m → ℝ := fun x j => ranZeroExtension (fun y => a y j) S x
  have hb : RanDefinableMap b := fun j => (ha j).zeroExtension hS
  apply (RanDefinableFun.ranDefinableOn
    (ranDefinableFun_weierstrassPolynomial_iterate_derivative_eval hb
      (ht.zeroExtension hS) k) hS).congr
  intro x hx
  have he : b x = a x := by funext j; simp only [b, ranZeroExtension, if_pos hx]
  simp only [he, ranZeroExtension, if_pos hx]

theorem ranDefinableOn_oneDimensionalSign_eq {ι : Type*}
    {f : (ι → ℝ) → ℝ} {S : Set (ι → ℝ)} (hS : RanDefinable S)
    (hf : RanDefinableOn f S) (s : Fin 3) :
    RanDefinable {x | x ∈ S ∧ oneDimensionalSign (f x) = s} := by
  convert hS.inter (ranDefinable_oneDimensionalSign_eq (hf.zeroExtension hS) s) using 1
  ext x
  by_cases hx : x ∈ S <;> simp [ranZeroExtension, hx]

theorem ranDefinable_polynomialThomRootRelation {ι : Type*} [Finite ι]
    {m : ℕ} {a : (ι → ℝ) → Fin m → ℝ} (ha : RanDefinableMap a)
    (s : Fin (m + 1) → Fin 3) :
    RanDefinable {w : Option ι → ℝ |
      (weierstrassPolynomial (a (w ∘ some))).eval (w none) = 0 ∧
        polynomialThomCode (weierstrassPolynomial (a (w ∘ some))) m (w none) = s} := by
  have hb : RanDefinableMap (fun w : Option ι → ℝ => a (w ∘ some)) :=
    fun j => (ha j).comp (fun i => ranDefinableFun_coordinate (some i))
  have hzero := (ranDefinableFun_weierstrassPolynomial_eval hb
    (ranDefinableFun_coordinate none)).setOf_eq (ranDefinableFun_const 0)
  have hsign (k : Fin (m + 1)) := ranDefinable_oneDimensionalSign_eq
    (ranDefinableFun_weierstrassPolynomial_iterate_derivative_eval hb
      (ranDefinableFun_coordinate none) k.val) (s k)
  convert hzero.inter (Set.definable_iInter_of_finite hsign) using 1
  ext w
  simp only [mem_setOf_eq, mem_inter_iff, mem_iInter, polynomialThomCode, funext_iff]

theorem ranDefinable_polynomialThomRootDomain {ι : Type*} [Finite ι]
    {m : ℕ} {a : (ι → ℝ) → Fin m → ℝ} (ha : RanDefinableMap a)
    (s : Fin (m + 1) → Fin 3) : RanDefinable (polynomialThomRootDomain a s) :=
  ranDefinable_exists_real (ranDefinable_polynomialThomRootRelation ha s)

theorem ranDefinableOn_polynomialThomRoot_global {ι : Type*} [Finite ι]
    {m : ℕ} {a : (ι → ℝ) → Fin m → ℝ} (ha : RanDefinableMap a)
    (s : Fin (m + 1) → Fin 3) :
    RanDefinableOn (polynomialThomRoot a s) (polynomialThomRootDomain a s) := by
  unfold RanDefinableOn
  convert ((ranDefinable_polynomialThomRootDomain ha s).preimage_comp some).inter
    (ranDefinable_polynomialThomRootRelation ha s) using 1
  ext w
  simp only [mem_setOf_eq, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨hx, he⟩
    exact ⟨hx, (polynomialThomRoot_graph_iff a s hx (w none)).mpr he.symm⟩
  · rintro ⟨hx, ht⟩
    exact ⟨hx, ((polynomialThomRoot_graph_iff a s hx (w none)).mp ht).symm⟩

theorem ranDefinable_polynomialThomRootDomain_on {ι : Type*} [Finite ι]
    {m : ℕ} {a : (ι → ℝ) → Fin m → ℝ} {S : Set (ι → ℝ)}
    (hS : RanDefinable S) (ha : ∀ j, RanDefinableOn (fun x => a x j) S)
    (s : Fin (m + 1) → Fin 3) : RanDefinable (S ∩ polynomialThomRootDomain a s) := by
  classical
  let b : (ι → ℝ) → Fin m → ℝ := fun x j => ranZeroExtension (fun y => a y j) S x
  have hb : RanDefinableMap b := fun j => (ha j).zeroExtension hS
  convert hS.inter (ranDefinable_polynomialThomRootDomain hb s) using 1
  ext x
  simp only [mem_inter_iff, polynomialThomRootDomain, mem_setOf_eq]
  apply and_congr_right
  intro hx
  have he : b x = a x := by funext j; simp only [b, ranZeroExtension, if_pos hx]
  rw [he]

theorem ranDefinableOn_polynomialThomRoot {ι : Type*} [Finite ι]
    {m : ℕ} {a : (ι → ℝ) → Fin m → ℝ} {S : Set (ι → ℝ)}
    (hS : RanDefinable S) (ha : ∀ j, RanDefinableOn (fun x => a x j) S)
    (s : Fin (m + 1) → Fin 3) :
    RanDefinableOn (polynomialThomRoot a s) (S ∩ polynomialThomRootDomain a s) := by
  classical
  let b : (ι → ℝ) → Fin m → ℝ := fun x j => ranZeroExtension (fun y => a y j) S x
  have hb : RanDefinableMap b := fun j => (ha j).zeroExtension hS
  have he (x : ι → ℝ) (hx : x ∈ S) : b x = a x := by
    funext j
    simp only [b, ranZeroExtension, if_pos hx]
  have hD := ranDefinable_polynomialThomRootDomain_on hS ha s
  have hm : S ∩ polynomialThomRootDomain a s ⊆ polynomialThomRootDomain b s := by
    intro x hx
    change ∃ t, (weierstrassPolynomial (b x)).eval t = 0 ∧ _
    rw [he x hx.1]
    exact hx.2
  apply ((ranDefinableOn_polynomialThomRoot_global hb s).restrict hD hm).congr
  intro x hx
  apply (polynomialThomRoot_graph_iff a s hx.2 _).mp
  have hs := polynomialThomRoot_spec b s (hm hx)
  rw [he x hx.1] at hs
  exact hs

end PlanarNikodym
