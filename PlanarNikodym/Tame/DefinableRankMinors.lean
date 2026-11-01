import PlanarNikodym.Tame.DefinableCalculus
import PlanarNikodym.Tame.FamilyStability
import PlanarNikodym.Rank.FiniteRankMinors

/-! Actual derivative evaluations used by rank decomposition are definable
in R_an. Analyticity supplies differentiability, not new language symbols. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set

namespace PlanarNikodym

theorem ranDefinableFun_finset_sum {ι J : Type*} (s : Finset J)
    {f : J → (ι → ℝ) → ℝ} (hf : ∀ j ∈ s, RanDefinableFun (f j)) :
    RanDefinableFun (fun x => ∑ j ∈ s, f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using ranDefinableFun_const (ι := ι) 0
  | @insert j s hjs ih =>
    simpa only [Finset.sum_insert hjs] using
      ranDefinableFun_add (hf j (Finset.mem_insert_self j s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem ranDefinableFun_finset_prod {ι J : Type*} (s : Finset J)
    {f : J → (ι → ℝ) → ℝ} (hf : ∀ j ∈ s, RanDefinableFun (f j)) :
    RanDefinableFun (fun x => ∏ j ∈ s, f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using ranDefinableFun_const (ι := ι) 1
  | @insert j s hjs ih =>
    simpa only [Finset.prod_insert hjs] using
      ranDefinableFun_mul (hf j (Finset.mem_insert_self j s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem ranDefinableFun_det {ι J : Type*} [Fintype J] [DecidableEq J]
    {A : (ι → ℝ) → Matrix J J ℝ} (hA : ∀ i j, RanDefinableFun (fun x => A x i j)) :
    RanDefinableFun (fun x => (A x).det) := by
  classical
  simp only [Matrix.det_apply']
  exact ranDefinableFun_finset_sum Finset.univ (fun σ _ =>
    ranDefinableFun_mul (ranDefinableFun_const _)
      (ranDefinableFun_finset_prod Finset.univ (fun i _ => hA (σ i) i)))

theorem ranDefinableOn_det {ι J : Type*} [Finite ι] [Fintype J] [DecidableEq J]
    {S : Set (ι → ℝ)} (hS : RanDefinable S)
    {A : (ι → ℝ) → Matrix J J ℝ} (hA : ∀ i j, RanDefinableOn (fun x => A x i j) S) :
    RanDefinableOn (fun x => (A x).det) S := by
  have hpoly : RanDefinableFun
      (fun a : (J × J) → ℝ => Matrix.det (fun i j => a (i, j))) :=
    ranDefinableFun_det (fun i j => ranDefinableFun_coordinate (i, j))
  exact (hpoly.ranDefinableOn Set.definable_univ).comp_on hS
    (fun i => hA i.1 i.2) (fun _ _ => mem_univ _)

theorem EvaluationMinor.ranDefinableOn {ι : Type*} [Finite ι]
    {n : ℕ} {X : Type*} (M : EvaluationMinor n X)
    {f : Fin n → X → (ι → ℝ) → ℝ} {S : Set (ι → ℝ)}
    (hS : RanDefinable S) (hf : ∀ j t, RanDefinableOn (f j t) S) :
    RanDefinableOn (M.value f) S :=
  ranDefinableOn_det hS (fun i j => hf (M.column j) (M.time i))

theorem RanDefinableOn.nonzero {ι : Type*} [Finite ι]
    {f : (ι → ℝ) → ℝ} {S : Set (ι → ℝ)}
    (hf : RanDefinableOn f S) (hS : RanDefinable S) :
    RanDefinable {x | x ∈ S ∧ f x ≠ 0} := by
  have hz := ((hf.zeroExtension hS).setOf_eq (ranDefinableFun_const 0)).compl
  convert hS.inter hz using 1
  ext x
  apply and_congr_right
  intro hx
  simp only [mem_setOf_eq, mem_compl_iff, ranZeroExtension, if_pos hx]

theorem Family.RanTame.parameter_value {d : ℕ} {G : Family 2 d}
    (hG : G.RanTame) (t : G.I.carrier) :
    RanDefinableOn (fun x => G.γ t (ranParameterEquiv d x))
      (ranParameterEquiv d ⁻¹' G.W) := by
  have hmap : RanDefinableMap (fun x : RanParameterIndex d → ℝ =>
      fun i => Option.elim i (t : ℝ) x) := by
    intro i
    cases i with
    | none => exact ranDefinableFun_const t
    | some i => exact ranDefinableFun_coordinate i
  exact (hG.2.preimage_map hmap).restrict hG.1 (fun _ hx => ⟨t.property, hx⟩)

theorem Family.RanTame.parameter_derivative {d : ℕ} {G : Family 2 d}
    (hG : G.RanTame) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (t : G.I.carrier) (v : Parameters 2 d) :
    RanDefinableOn (fun x => fderiv ℝ (G.γ t) (ranParameterEquiv d x) v)
      (ranParameterEquiv d ⁻¹' G.W) := by
  let E := ranParameterEquiv d
  have hd (x : RanParameterIndex d → ℝ) (hx : x ∈ E ⁻¹' G.W) :
      DifferentiableAt ℝ (fun x => G.γ t (E x)) x :=
    (G.parameter_analytic ha (E x) hx t).differentiableAt.comp x E.differentiableAt
  apply ((hG.parameter_value t).directionalDerivative hG.1
    (ho.preimage E.continuous) hd (E.symm v)).congr
  intro x hx
  change fderiv ℝ (G.γ t ∘ E) x (E.symm v) = fderiv ℝ (G.γ t) (E x) v
  rw [fderiv_comp x (G.parameter_analytic ha (E x) hx t).differentiableAt
    E.differentiableAt]
  rw [E.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, E.apply_symm_apply]

theorem Family.RanTame.uColumn {d : ℕ} {G : Family 2 d}
    (hG : G.RanTame) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (j : Fin d) (t : G.I.carrier) :
    RanDefinableOn (fun x => G.uColumn (ranParameterEquiv d x) j t)
      (ranParameterEquiv d ⁻¹' G.W) := by
  apply (hG.parameter_derivative ho ha t (0, Pi.single j 1)).congr
  intro x hx
  exact (congrArg (fun L : Aux d →L[ℝ] ℝ => L (Pi.single j 1))
    (fderiv_snd_slice (G.γ t) (ranParameterEquiv d x)
      (G.parameter_analytic ha _ hx t).differentiableAt)).symm

theorem Family.RanTame.zColumn {d : ℕ} {G : Family 2 d}
    (hG : G.RanTame) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (j : Fin 2) (t : G.I.carrier) :
    RanDefinableOn (fun x => G.zColumn (ranParameterEquiv d x) j t)
      (ranParameterEquiv d ⁻¹' G.W) := by
  apply (hG.parameter_derivative ho ha t (Pi.single j 1, 0)).congr
  intro x hx
  exact (congrArg (fun L : Base 2 →L[ℝ] ℝ => L (Pi.single j 1))
    (fderiv_fst_slice (G.γ t) (ranParameterEquiv d x)
      (G.parameter_analytic ha _ hx t).differentiableAt)).symm

theorem Family.RanTame.totalColumn {d : ℕ} {G : Family 2 d}
    (hG : G.RanTame) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (j : Fin (d + 2)) (t : G.I.carrier) :
    RanDefinableOn (fun x => G.totalColumn (ranParameterEquiv d x) j t)
      (ranParameterEquiv d ⁻¹' G.W) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa only [Family.totalColumn, Fin.append_left] using hG.uColumn ho ha j t
  · simpa only [Family.totalColumn, Fin.append_right] using hG.zColumn ho ha j t

/-- Actual regular loci, including their derivative evaluations, are
definable before any cell decomposition is available. -/
theorem DoubleRankMinor.ranDefinable_regularSet {d : ℕ} {G : Family 2 d}
    (M : DoubleRankMinor G) (hG : G.RanTame) (ho : IsOpen G.W) (ha : G.IsAnalytic) :
    RanDefinable (ranParameterEquiv d ⁻¹' M.regularSet) := by
  have hp := M.point.ranDefinableOn hG.1 (hG.uColumn ho ha)
  have hc := M.curve.ranDefinableOn hG.1 (hG.totalColumn ho ha)
  convert (hp.nonzero hG.1).inter (hc.nonzero hG.1) using 1
  ext x
  simp only [DoubleRankMinor.regularSet, mem_preimage, mem_setOf_eq, mem_inter_iff,
    EvaluationMinor.value]
  tauto

end PlanarNikodym
