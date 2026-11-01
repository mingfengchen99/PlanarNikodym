import PlanarNikodym.Rank.Rank
import PlanarNikodym.Rank.FiniteEvaluation
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
open Set Submodule Module
namespace PlanarNikodym.Examples

abbrev horizontal (I : Interval) : Family 2 0 := ⟨I, univ, fun _ p => p.1 1⟩
abbrev slidingHorizontal (I : Interval) : Family 2 1 := ⟨I, univ, fun _ p => p.1 1 - p.2 0⟩
abbrev lines (I : Interval) : Family 2 1 :=
  ⟨I, univ, fun t p => p.1 1 + p.2 0 * (t - p.1 0)⟩

theorem horizontal_zColumn (I : Interval) (p : Parameters 2 0) :
    (horizontal I).zColumn p = ![fun _ : I.carrier => 0, fun _ => 1] := by
  funext i t
  change (fderiv ℝ (fun z : Base 2 => z 1) p.1) (Pi.single i 1) = ![fun _ : I.carrier => 0, fun _ => 1] i t
  rw [(hasFDerivAt_apply (𝕜 := ℝ) 1 p.1).fderiv]
  fin_cases i <;> simp

theorem sliding_uColumn (I : Interval) (p : Parameters 2 1) :
    (slidingHorizontal I).uColumn p = ![fun _ : I.carrier => -1] := by
  funext i t
  change (fderiv ℝ (fun u : Aux 1 => p.1 1 - u 0) p.2) (Pi.single i 1) = _
  have h : HasFDerivAt (fun u : Aux 1 => p.1 1 - u 0)
      (0 - ContinuousLinearMap.proj 0) p.2 :=
    (hasFDerivAt_const (𝕜 := ℝ) (p.1 1) p.2).sub (hasFDerivAt_apply (𝕜 := ℝ) 0 p.2)
  rw [h.fderiv]
  fin_cases i
  simp

theorem sliding_zColumn (I : Interval) (p : Parameters 2 1) :
    (slidingHorizontal I).zColumn p = ![fun _ : I.carrier => 0, fun _ => 1] := by
  funext i t
  change (fderiv ℝ (fun z : Base 2 => z 1 - p.2 0) p.1) (Pi.single i 1) = _
  have h : HasFDerivAt (fun z : Base 2 => z 1 - p.2 0)
      (ContinuousLinearMap.proj 1 - 0) p.1 :=
    (hasFDerivAt_apply (𝕜 := ℝ) 1 p.1).sub (hasFDerivAt_const (𝕜 := ℝ) (p.2 0) p.1)
  rw [h.fderiv]
  fin_cases i <;> simp

theorem lines_uColumn (I : Interval) (p : Parameters 2 1) :
    (lines I).uColumn p = ![fun t : I.carrier => (t : ℝ) - p.1 0] := by
  funext i t
  change (fderiv ℝ (fun u : Aux 1 => p.1 1 + u 0 * ((t : ℝ) - p.1 0)) p.2)
    (Pi.single i 1) = _
  have h : HasFDerivAt (fun u : Aux 1 => p.1 1 + u 0 * ((t : ℝ) - p.1 0))
      ((0 : Aux 1 →L[ℝ] ℝ) + ((t : ℝ) - p.1 0) • ContinuousLinearMap.proj (0 : Fin 1)) p.2 :=
    (hasFDerivAt_const (𝕜 := ℝ) (p.1 1) p.2).add
      ((hasFDerivAt_apply (𝕜 := ℝ) 0 p.2).mul_const ((t : ℝ) - p.1 0))
  rw [h.fderiv]
  fin_cases i
  simp

theorem lines_zColumn (I : Interval) (p : Parameters 2 1) :
    (lines I).zColumn p = ![fun _ : I.carrier => -p.2 0, fun _ => 1] := by
  funext i t
  change (fderiv ℝ (fun z : Base 2 => z 1 + p.2 0 * ((t : ℝ) - z 0)) p.1)
    (Pi.single i 1) = _
  have h : HasFDerivAt (fun z : Base 2 => z 1 + p.2 0 * ((t : ℝ) - z 0))
      ((ContinuousLinearMap.proj (1 : Fin 2) : Base 2 →L[ℝ] ℝ) + p.2 0 • ((0 : Base 2 →L[ℝ] ℝ) - ContinuousLinearMap.proj (0 : Fin 2))) p.1 :=
    (hasFDerivAt_apply (𝕜 := ℝ) 1 p.1).add
      (((hasFDerivAt_const (𝕜 := ℝ) (t : ℝ) p.1).sub
        (hasFDerivAt_apply (𝕜 := ℝ) 0 p.1)).const_mul (p.2 0))
  rw [h.fderiv]
  fin_cases i <;> simp

theorem one_function_ne_zero (I : Interval) : (1 : I.carrier → ℝ) ≠ 0 := by
  intro h
  have := congrFun h ⟨I.left, le_rfl, I.nondegenerate.le⟩
  norm_num at this

theorem horizontal_ranks (I : Interval) (p : Parameters 2 0) :
    (horizontal I).pointRank p = 0 ∧ (horizontal I).curveRank p = 1 := by
  refine ⟨Family.pointRank_zero_aux _ _, ?_⟩
  have hzero : (horizontal I).pointSpace p = ⊥ := by
    simp [Family.pointSpace, Set.range_eq_empty]
  rw [Family.curveRank, Family.curveSpace, hzero, bot_sup_eq, horizontal_zColumn]
  have hs : span ℝ (range (![fun _ : I.carrier => 0, fun _ => 1])) = ℝ ∙ (1 : I.carrier → ℝ) := by
    apply le_antisymm
    · apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact zero_mem _
      · exact subset_span (mem_singleton _)
    · apply span_le.mpr
      intro v hv
      have hv1 : v = 1 := mem_singleton_iff.mp hv
      rw [hv1]
      exact subset_span ⟨1, rfl⟩
  rw [hs]
  exact finrank_span_singleton (one_function_ne_zero I)

/-- Constants and the identity function on a nondegenerate interval have rank 2. -/
theorem independent_one_id (I : Interval) :
    LinearIndependent ℝ (![1, fun t : I.carrier => (t : ℝ)]) := by
  apply independent_of_eval_det_ne_zero _
    ![⟨I.left, le_rfl, I.nondegenerate.le⟩, ⟨I.right, I.nondegenerate.le, le_rfl⟩]
  simp [Matrix.det_fin_two]
  exact ne_of_gt (sub_pos.mpr I.nondegenerate)

theorem sliding_ranks (I : Interval) (p : Parameters 2 1) :
    (slidingHorizontal I).pointRank p = 1 ∧ (slidingHorizontal I).curveRank p = 1 := by
  have hp : (slidingHorizontal I).pointRank p = 1 := by
    rw [Family.pointRank, Family.pointSpace, sliding_uColumn, Set.range_unique]
    change finrank ℝ (ℝ ∙ (-1 : I.carrier → ℝ)) = 1
    exact finrank_span_singleton (neg_ne_zero.mpr (one_function_ne_zero I))
  refine ⟨hp, ?_⟩
  have hcurve : (slidingHorizontal I).curveSpace p = ℝ ∙ (1 : I.carrier → ℝ) := by
    apply le_antisymm
    · apply sup_le
      · apply span_le.mpr
        rintro _ ⟨i, rfl⟩
        rw [sliding_uColumn]
        fin_cases i
        exact (ℝ ∙ (1 : I.carrier → ℝ)).neg_mem (mem_span_singleton_self _)
      · apply span_le.mpr
        rintro _ ⟨i, rfl⟩
        rw [sliding_zColumn]
        fin_cases i
        · exact zero_mem _
        · exact mem_span_singleton_self _
    · apply (span_singleton_le_iff_mem _ _).mpr
      apply Submodule.mem_sup_right
      exact subset_span ⟨1, by rw [sliding_zColumn]; rfl⟩
  rw [Family.curveRank, hcurve]
  exact finrank_span_singleton (one_function_ne_zero I)

theorem lines_ranks (I : Interval) (p : Parameters 2 1) :
    (lines I).pointRank p = 1 ∧ (lines I).curveRank p = 2 := by
  letI := Family.pointSpace_finite (lines I) p
  letI := Family.curveSpace_finite (lines I) p
  letI := FiniteDimensional.span_of_finite ℝ (Set.finite_range ((lines I).zColumn p))
  have hp : (lines I).pointRank p = 1 := by
    rw [Family.pointRank, Family.pointSpace, lines_uColumn, Set.range_unique]
    change finrank ℝ (ℝ ∙ (fun t : I.carrier => (t : ℝ) - p.1 0)) = 1
    apply finrank_span_singleton
    intro h
    have ha := congrFun h ⟨I.left, le_rfl, I.nondegenerate.le⟩
    have hb := congrFun h ⟨I.right, I.nondegenerate.le, le_rfl⟩
    have hab := I.nondegenerate
    simp only [Pi.zero_apply] at ha hb
    linarith
  refine ⟨hp, ?_⟩
  have h1 : (1 : I.carrier → ℝ) ∈ (lines I).curveSpace p := by
    apply Submodule.mem_sup_right
    exact subset_span ⟨1, by rw [lines_zColumn]; rfl⟩
  have hu : (fun t : I.carrier => (t : ℝ) - p.1 0) ∈ (lines I).curveSpace p := by
    apply Submodule.mem_sup_left
    exact subset_span ⟨0, by rw [lines_uColumn]; rfl⟩
  have ht : (fun t : I.carrier => (t : ℝ)) ∈ (lines I).curveSpace p := by
    convert (lines I).curveSpace p |>.add_mem hu (((lines I).curveSpace p).smul_mem (p.1 0) h1) using 1
    ext t
    simp
  have hs : span ℝ (range (![1, fun t : I.carrier => (t : ℝ)])) ≤ (lines I).curveSpace p := by
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h1
    · exact ht
  have hl := Submodule.finrank_mono hs
  have hr : finrank ℝ (span ℝ (range (![1, fun t : I.carrier => (t : ℝ)]))) = 2 := by
    simpa using finrank_span_eq_card (independent_one_id I)
  rw [hr] at hl
  have hparam : (lines I).curveRank p ≤ 2 := by
    have hz : finrank ℝ (span ℝ (range ((lines I).zColumn p))) ≤ 1 := by
      have hs1 : span ℝ (range ((lines I).zColumn p)) ≤ ℝ ∙ (1 : I.carrier → ℝ) := by
        apply span_le.mpr
        rintro _ ⟨i, rfl⟩
        rw [lines_zColumn]
        fin_cases i
        · change (fun _ : I.carrier => -p.2 0) ∈ ℝ ∙ (1 : I.carrier → ℝ)
          rw [Submodule.mem_span_singleton]
          exact ⟨-p.2 0, by ext t; simp⟩
        · exact mem_span_singleton_self _
      have hd := Submodule.finrank_mono hs1
      rw [finrank_span_singleton (one_function_ne_zero I)] at hd
      exact hd
    have hd := Submodule.finrank_add_le_finrank_add_finrank
      ((lines I).pointSpace p) (span ℝ (range ((lines I).zColumn p)))
    change (lines I).curveRank p ≤ (lines I).pointRank p +
      finrank ℝ (span ℝ (range ((lines I).zColumn p))) at hd
    rw [hp] at hd
    omega
  exact Nat.le_antisymm hparam hl

/-- A small polynomial family checks the finite-evaluation theorem directly. -/
theorem polynomial_eval_det :
    Matrix.det (fun i j : Fin 3 => (![fun _ : ℝ => 1, id, fun t => t ^ 2] j)
      (![0, 1, 2] i)) = 2 := by
  norm_num [Matrix.det_fin_three, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two]

theorem polynomial_independent :
    LinearIndependent ℝ (![fun _ : ℝ => 1, id, fun t => t ^ 2]) := by
  apply independent_of_eval_det_ne_zero _ (![0, 1, 2])
  rw [polynomial_eval_det]
  norm_num

theorem polynomial_rank :
    finrank ℝ (span ℝ (range (![fun _ : ℝ => 1, id, fun t => t ^ 2]))) = 3 := by
  simpa using finrank_span_eq_card polynomial_independent

theorem empty_evaluation : ∃ x : Fin 0 → Empty,
    Matrix.det (fun i j => (Fin.elim0 j : Empty → ℝ) (x i)) ≠ 0 :=
  exists_eval_det_ne_zero (fun j => Fin.elim0 j) linearIndependent_empty_type

end PlanarNikodym.Examples
