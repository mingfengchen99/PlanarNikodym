import PlanarNikodym.Analysis.Fourier.MixedMomentTransversality

/-! Identification with the actual, unnormalized GLYZ moment curve
Gamma(t) = (t, t², ..., t^m). -/
noncomputable section
open Polynomial Set Metric
open scoped Matrix.Norms.Elementwise
namespace PlanarNikodym

theorem mixedJetFlatten_apply_left (l r : ℕ) (v : Aux l × Aux r) (j : Fin l) :
    mixedJetFlatten l r v (j.castAdd r) = v.1 j := by
  change (Equiv.piCongrLeft (fun _ : Fin (l + r) => ℝ) finSumFinEquiv)
    ((LinearEquiv.sumArrowLequivProdArrow (Fin l) (Fin r) ℝ ℝ).symm v) (j.castAdd r) = _
  rw [Equiv.piCongrLeft_apply]
  simp only [eq_rec_constant, finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem mixedJetFlatten_apply_right (l r : ℕ) (v : Aux l × Aux r) (j : Fin r) :
    mixedJetFlatten l r v (j.natAdd l) = v.2 j := by
  change (Equiv.piCongrLeft (fun _ : Fin (l + r) => ℝ) finSumFinEquiv)
    ((LinearEquiv.sumArrowLequivProdArrow (Fin l) (Fin r) ℝ ℝ).symm v) (j.natAdd l) = _
  rw [Equiv.piCongrLeft_apply]
  simp only [eq_rec_constant, finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem degreeLTEquiv_symm_single {m : ℕ} (j : Fin m) :
    ((Polynomial.degreeLTEquiv ℝ m).symm (Pi.single j 1)).1 = X ^ (j : ℕ) := by
  change (∑ i : Fin m, monomial (i : ℕ) (Pi.single j (1 : ℝ) i)) = X ^ (j : ℕ)
  classical
  rw [Finset.sum_eq_single j]
  · simpa only [Pi.single_eq_same] using Polynomial.monomial_one_right_eq_X_pow (j : ℕ)
  · intro i _ hij
    simp [hij]
  · simp

theorem mixedDerivativeMatrix_apply_left (l r : ℕ) (s t : ℝ) (j : Fin l) (k : Fin (l + r)) :
    mixedDerivativeMatrix l r s t (j.castAdd r) k =
      iteratedDeriv j (fun x : ℝ => x ^ (k : ℕ)) s := by
  change mixedJetFlatten l r (mixedDerivativeJetMap l r s t
    ((Polynomial.degreeLTEquiv ℝ (l + r)).symm (Pi.single k 1))) (j.castAdd r) = _
  rw [mixedJetFlatten_apply_left, mixedDerivativeJetMap_apply_left, degreeLTEquiv_symm_single]
  simp only [Polynomial.eval_pow, Polynomial.eval_X]

theorem mixedDerivativeMatrix_apply_right (l r : ℕ) (s t : ℝ) (j : Fin r) (k : Fin (l + r)) :
    mixedDerivativeMatrix l r s t (j.natAdd l) k =
      iteratedDeriv j (fun x : ℝ => x ^ (k : ℕ)) t := by
  change mixedJetFlatten l r (mixedDerivativeJetMap l r s t
    ((Polynomial.degreeLTEquiv ℝ (l + r)).symm (Pi.single k 1))) (j.natAdd l) = _
  rw [mixedJetFlatten_apply_right, mixedDerivativeJetMap_apply_right, degreeLTEquiv_symm_single]
  simp only [Polynomial.eval_pow, Polynomial.eval_X]

def glyzMomentCurve (m : ℕ) (t : ℝ) : Base m := fun k => t ^ ((k : ℕ) + 1)

def glyzMixedMomentMatrix (l r : ℕ) (s t : ℝ) :
    Matrix (Fin (l + r)) (Fin (l + r)) ℝ :=
  Matrix.diagonal (fun k : Fin (l + r) => ((k : ℕ) + 1 : ℝ)) *
    (mixedDerivativeMatrix l r s t).transpose

theorem iteratedDeriv_monomial_succ (j k : ℕ) (s : ℝ) :
    iteratedDeriv (j + 1) (fun x : ℝ => x ^ (k + 1)) s =
      ((k + 1 : ℕ) : ℝ) * iteratedDeriv j (fun x : ℝ => x ^ k) s := by
  rw [iteratedDeriv_succ']
  have he : deriv (fun x : ℝ => x ^ (k + 1)) = fun x => ((k + 1 : ℕ) : ℝ) * x ^ k := by
    funext x
    simp [deriv_fun_pow]
  rw [he, iteratedDeriv_const_mul_field]

/-- The left block consists of Gamma'(s), ..., Gamma^(l)(s). -/
theorem glyzMixedMomentMatrix_apply_left (l r : ℕ) (s t : ℝ) (j : Fin l) (k : Fin (l + r)) :
    glyzMixedMomentMatrix l r s t k (j.castAdd r) =
      iteratedDeriv ((j : ℕ) + 1) (fun x => glyzMomentCurve (l + r) x k) s := by
  simp only [glyzMixedMomentMatrix, Matrix.diagonal_mul, Matrix.transpose_apply,
    mixedDerivativeMatrix_apply_left, glyzMomentCurve]
  simpa only [Nat.cast_add, Nat.cast_one] using (iteratedDeriv_monomial_succ j k s).symm

/-- The right block consists of Gamma'(t), ..., Gamma^(r)(t). -/
theorem glyzMixedMomentMatrix_apply_right (l r : ℕ) (s t : ℝ) (j : Fin r) (k : Fin (l + r)) :
    glyzMixedMomentMatrix l r s t k (j.natAdd l) =
      iteratedDeriv ((j : ℕ) + 1) (fun x => glyzMomentCurve (l + r) x k) t := by
  simp only [glyzMixedMomentMatrix, Matrix.diagonal_mul, Matrix.transpose_apply,
    mixedDerivativeMatrix_apply_right, glyzMomentCurve]
  simpa only [Nat.cast_add, Nat.cast_one] using (iteratedDeriv_monomial_succ j k t).symm

theorem det_glyzMixedMomentMatrix_ne_zero (l r : ℕ) {s t : ℝ} (hst : s ≠ t) :
    (glyzMixedMomentMatrix l r s t).det ≠ 0 := by
  rw [glyzMixedMomentMatrix, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
  apply mul_ne_zero _ (det_mixedDerivativeMatrix_ne_zero l r hst)
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => by positivity)

def glyzMomentJetBlock (m q : ℕ) (s : ℝ) (j : Fin q) : Base m :=
  fun k => iteratedDeriv ((j : ℕ) + 1) (fun x => glyzMomentCurve m x k) s

def glyzTangentSpace (m q : ℕ) (s : ℝ) : Submodule ℝ (Base m) :=
  Submodule.span ℝ (Set.range (glyzMomentJetBlock m q s))

theorem linearIndependent_glyzMixedMomentJets (l r : ℕ) {s t : ℝ} (hst : s ≠ t) :
    LinearIndependent ℝ (Sum.elim (glyzMomentJetBlock (l + r) l s)
      (glyzMomentJetBlock (l + r) r t)) := by
  have h := (Matrix.linearIndependent_cols_of_det_ne_zero
    (det_glyzMixedMomentMatrix_ne_zero l r hst)).comp
      finSumFinEquiv finSumFinEquiv.injective
  have he : (glyzMixedMomentMatrix l r s t).col ∘ finSumFinEquiv =
      Sum.elim (glyzMomentJetBlock (l + r) l s) (glyzMomentJetBlock (l + r) r t) := by
    funext j
    cases j with
    | inl j =>
      ext k
      exact glyzMixedMomentMatrix_apply_left l r s t j k
    | inr j =>
      ext k
      exact glyzMixedMomentMatrix_apply_right l r s t j k
  rwa [he] at h

/-- The l jets remain independent after quotienting out the r tangent
directions at the other center. This is the algebraic projected torsion
statement, prior to selecting an orthonormal coordinate frame. -/
theorem linearIndependent_glyzProjectedMomentJets (l r : ℕ) {s t : ℝ} (hst : s ≠ t) :
    LinearIndependent ℝ ((glyzTangentSpace (l + r) r t).mkQ ∘
      glyzMomentJetBlock (l + r) l s) := by
  have hi := linearIndependent_sum.mp (linearIndependent_glyzMixedMomentJets l r hst)
  apply ((glyzTangentSpace (l + r) r t).mkQ.linearIndependent_iff_of_disjoint ?_).mpr hi.1
  change Disjoint (Submodule.span ℝ (Set.range (glyzMomentJetBlock (l + r) l s)))
    (LinearMap.ker (Submodule.span ℝ (Set.range (glyzMomentJetBlock (l + r) r t))).mkQ)
  rw [Submodule.ker_mkQ]
  simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr] using hi.2.2

theorem continuous_glyzMixedMomentMatrix (l r : ℕ) :
    Continuous (fun z : ℝ × ℝ => glyzMixedMomentMatrix l r z.1 z.2) :=
  continuous_const.matrix_mul (continuous_mixedDerivativeMatrix l r).matrix_transpose

/-- The transversality needed for separated bilinear intervals is uniform
and remains true under one uniformly chosen matrix perturbation. -/
theorem exists_uniform_glyzMixedMoment_perturbation (l r : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∃ b ε : ℝ, 0 < b ∧ 0 < ε ∧
      ∀ z ∈ separatedMixedCenters ν,
        ∀ M : Matrix (Fin (l + r)) (Fin (l + r)) ℝ,
          dist M (glyzMixedMomentMatrix l r z.1 z.2) < ε → b ≤ |M.det| := by
  let K := (fun z : ℝ × ℝ => glyzMixedMomentMatrix l r z.1 z.2) '' separatedMixedCenters ν
  have hK : IsCompact K := (isCompact_separatedMixedCenters ν).image
    (continuous_glyzMixedMomentMatrix l r)
  have hn : ∀ M ∈ K, 0 < |M.det| := by
    rintro _ ⟨z, hz, rfl⟩
    apply abs_pos.mpr (det_glyzMixedMomentMatrix_ne_zero l r ?_)
    intro he
    have : ν ≤ 0 := by simpa [he] using hz.2.2
    exact (not_le_of_gt hν) this
  by_cases he : K.Nonempty
  · obtain ⟨M₀, hM₀, hmin⟩ := hK.exists_isMinOn he continuous_id.matrix_det.abs.continuousOn
    have hb := hn M₀ hM₀
    have ho : IsOpen {M : Matrix (Fin (l + r)) (Fin (l + r)) ℝ |
        |M₀.det| / 2 < |M.det|} :=
      isOpen_lt continuous_const continuous_id.matrix_det.abs
    obtain ⟨ε, hε, hstable⟩ := hK.exists_thickening_subset_open ho
      (fun M hM => (half_lt_self hb).trans_le (hmin hM))
    refine ⟨|M₀.det| / 2, ε, half_pos hb, hε, ?_⟩
    intro z hz M hM
    exact (hstable (mem_thickening_iff.mpr
      ⟨glyzMixedMomentMatrix l r z.1 z.2, ⟨z, hz, rfl⟩, hM⟩)).le
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro z hz
    exact (he ⟨_, ⟨z, hz, rfl⟩⟩).elim

end PlanarNikodym
