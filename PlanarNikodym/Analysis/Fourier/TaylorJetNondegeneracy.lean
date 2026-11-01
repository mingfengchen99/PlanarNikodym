import PlanarNikodym.Analysis.Fourier.NormalizedTaylorRemainder
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Actual finite jets of time Taylor polynomials, their parameter
Jacobians, and preservation of nondegeneracy near the Taylor center. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology Nat

namespace PlanarNikodym

theorem contDiff_timeTaylorEval_time {P : Type} (Φ : P × ℝ → ℝ)
    (n : ℕ) (p : P) (c : ℝ) : ContDiff ℝ ∞ (timeTaylorEval Φ n p c) := by
  unfold timeTaylorEval
  fun_prop

/-- The Taylor polynomial has precisely the original time jets at its
center through the retained degree. No regularity assumption is needed
for this algebraic identity between its actual derivatives. -/
theorem iteratedDeriv_timeTaylorEval_center {P : Type} (Φ : P × ℝ → ℝ)
    (n m : ℕ) (p : P) (c : ℝ) (hm : m ≤ n) :
    iteratedDeriv m (timeTaylorEval Φ n p c) c = iteratedDeriv m (fun s => Φ (p, s)) c := by
  have he : timeTaylorEval Φ n p c = fun t => ∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i (fun s => Φ (p, s)) c / (i ! : ℝ)) * (t - c) ^ i := by
    funext t
    unfold timeTaylorEval
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hterm (i : ℕ) : iteratedDeriv m (fun t =>
      (iteratedDeriv i (fun s => Φ (p, s)) c / (i ! : ℝ)) * (t - c) ^ i) c =
      (iteratedDeriv i (fun s => Φ (p, s)) c / (i ! : ℝ)) *
        (if m = i then (i ! : ℝ) else 0) := by
    rw [iteratedDeriv_const_mul_field]
    have hp := congrFun (iteratedDeriv_comp_sub_const m (fun y : ℝ => y ^ i) c) c
    simpa only [sub_self, iteratedDeriv_fun_pow_zero, apply_ite, Nat.cast_zero] using congrArg
      (fun z : ℝ => (iteratedDeriv i (fun s => Φ (p, s)) c / (i ! : ℝ)) * z) hp
  rw [he, iteratedDeriv_fun_sum (by intro i _; fun_prop)]
  simp_rw [hterm]
  rw [Finset.sum_eq_single m]
  · simp only [ite_true]
    exact div_mul_cancel₀ _ (by positivity)
  · intro i _ him
    simp only [if_neg (Ne.symm him), mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

theorem iteratedDeriv_timeTaylorEval_rescaled_center {P : Type} (Φ : P × ℝ → ℝ)
    (n m : ℕ) (p : P) (c δ : ℝ) (hm : m ≤ n) :
    iteratedDeriv m (fun τ => timeTaylorEval Φ n p c (c + δ * τ)) 0 =
      δ ^ m * iteratedDeriv m (fun s => Φ (p, s)) c := by
  have hT : ContDiff ℝ m (fun t => timeTaylorEval Φ n p c (c + t)) :=
    contDiff_infty.mp ((contDiff_timeTaylorEval_time Φ n p c).comp
      (contDiff_const.add contDiff_id)) m
  rw [congrFun (iteratedDeriv_comp_const_mul hT δ) 0]
  rw [iteratedDeriv_comp_const_add m (timeTaylorEval Φ n p c) c]
  simp only [mul_zero, add_zero, iteratedDeriv_timeTaylorEval_center Φ n m p c hm]

/-- The actual finite time-jet parameter matrix in a selected list of
parameter directions. This includes square minors of a larger family. -/
def timeJetParameterMatrix {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : P × ℝ → ℝ) (N : ℕ) (v : Fin N → P) (c : ℝ) (p : P) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => fderiv ℝ (fun q => iteratedDeriv i (fun s => Φ (q, s)) c) p (v j)

/-- Taylor truncation preserves every retained parameter minor at the
center, as an equality of actual derivative matrices. -/
theorem timeJetParameterMatrix_timeTaylorEval_center
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : P × ℝ → ℝ) (n N : ℕ) (v : Fin N → P) (c : ℝ) (p : P) (hN : N ≤ n + 1) :
    timeJetParameterMatrix (fun x => timeTaylorEval Φ n x.1 c x.2) N v c p =
      timeJetParameterMatrix Φ N v c p := by
  ext i j
  have he : (fun q => iteratedDeriv i (fun s => timeTaylorEval Φ n q c s) c) =
      fun q => iteratedDeriv i (fun s => Φ (q, s)) c := by
    funext q
    exact iteratedDeriv_timeTaylorEval_center Φ n i q c (by omega)
  change fderiv ℝ _ p (v j) = _
  rw [he]
  rfl

/-- Time rescaling multiplies the actual parameter rows by the expected
powers of the scale. The parameter directions themselves are retained. -/
theorem timeJetParameterMatrix_rescaled_timeTaylorEval_center
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n N : ℕ)
    (v : Fin N → P) (c δ : ℝ) (p : P) (hN : N ≤ n + 1) :
    timeJetParameterMatrix (fun x => timeTaylorEval Φ n x.1 c (c + δ * x.2)) N v 0 p =
      fun i j : Fin N => δ ^ (i : ℕ) * timeJetParameterMatrix Φ N v c p i j := by
  ext i j
  have he : (fun q => iteratedDeriv i (fun τ => timeTaylorEval Φ n q c (c + δ * τ)) 0) =
      fun q => δ ^ (i : ℕ) * iteratedDeriv i (fun s => Φ (q, s)) c := by
    funext q
    exact iteratedDeriv_timeTaylorEval_rescaled_center Φ n i q c δ (by omega)
  have hD : ContDiff ℝ ∞ (iteratedPartialTimeDeriv i Φ) :=
    contDiff_iff_contDiffAt.mpr (fun _ => contDiffAt_iteratedPartialTimeDeriv hΦ.contDiffAt i)
  have hd : DifferentiableAt ℝ (fun q => iteratedDeriv i (fun s => Φ (q, s)) c) p := by
    simpa only [Function.comp_def, id_eq, iteratedPartialTimeDeriv_apply] using
      ((hD.comp (contDiff_id.prodMk (contDiff_const (c := c)))).differentiable (by simp) p)
  change fderiv ℝ _ p (v j) = _
  rw [he, fderiv_const_mul hd]
  rfl

theorem det_timeJetParameterMatrix_rescaled_timeTaylorEval_center
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n N : ℕ)
    (v : Fin N → P) (c δ : ℝ) (p : P) (hN : N ≤ n + 1) :
    (timeJetParameterMatrix (fun x => timeTaylorEval Φ n x.1 c (c + δ * x.2)) N v 0 p).det =
      (∏ i : Fin N, δ ^ (i : ℕ)) * (timeJetParameterMatrix Φ N v c p).det := by
  rw [timeJetParameterMatrix_rescaled_timeTaylorEval_center hΦ n N v c δ p hN]
  exact Matrix.det_mul_column _ _

theorem contDiff_joint_timeTaylorEval
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n : ℕ) :
    ContDiff ℝ ∞ (fun x : (P × ℝ) × ℝ => timeTaylorEval Φ n x.1.1 x.1.2 x.2) := by
  have hD (i : ℕ) : ContDiff ℝ ∞ (iteratedPartialTimeDeriv i Φ) :=
    contDiff_iff_contDiffAt.mpr (fun _ => contDiffAt_iteratedPartialTimeDeriv hΦ.contDiffAt i)
  have he : (fun x : (P × ℝ) × ℝ => timeTaylorEval Φ n x.1.1 x.1.2 x.2) =
      fun x => ∑ i ∈ Finset.range (n + 1),
        iteratedPartialTimeDeriv i Φ x.1 * (x.2 - x.1.2) ^ i / (i ! : ℝ) := by
    funext ⟨⟨p, c⟩, t⟩
    simp only [timeTaylorEval, iteratedPartialTimeDeriv_apply]
  rw [he]
  apply ContDiff.sum
  intro i _
  exact (((hD i).comp contDiff_fst).mul
    ((contDiff_snd.sub contDiff_fst.snd).pow i)).div_const _

/-- Joint continuity of the parameter minor of the Taylor polynomial,
with the Taylor center and evaluation time both varying. -/
theorem continuous_timeTaylorJetParameterMatrix
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n N : ℕ) (v : Fin N → P) :
    Continuous (fun x : (P × ℝ) × ℝ =>
      timeJetParameterMatrix (fun y => timeTaylorEval Φ n y.1 x.1.2 y.2) N v x.2 x.1.1) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  let T : (P × ℝ) × ℝ → ℝ := fun x => timeTaylorEval Φ n x.1.1 x.1.2 x.2
  have hT := contDiff_joint_timeTaylorEval hΦ n
  have hD : ContDiff ℝ ∞ (iteratedPartialTimeDeriv i T) :=
    contDiff_iff_contDiffAt.mpr (fun _ => contDiffAt_iteratedPartialTimeDeriv hT.contDiffAt i)
  let H : P × (ℝ × ℝ) → ℝ := fun x => iteratedPartialTimeDeriv i T ((x.1, x.2.1), x.2.2)
  have hH : ContDiff ℝ ∞ H := hD.comp (by fun_prop)
  have hJ : Continuous (fun x : P × (ℝ × ℝ) =>
      fderiv ℝ (fun q => H (q, x.2)) x.1) :=
    continuous_iff_continuousAt.mpr (fun _ =>
      (contDiffAt_fiber_fderiv hH.contDiffAt).continuousAt)
  have harg : Continuous (fun x : (P × ℝ) × ℝ => (x.1.1, x.1.2, x.2)) := by fun_prop
  have happ := ((ContinuousLinearMap.apply ℝ ℝ (v j)).continuous.comp (hJ.comp harg))
  convert happ using 1
  funext x
  simp only [timeJetParameterMatrix, H, iteratedPartialTimeDeriv_apply, T]
  rfl

/-- A nonzero retained minor on a compact set stays nonzero on every
normalized unit time slice at sufficiently small scale, uniformly in
the Taylor center and all the parameters in that compact set. -/
theorem exists_uniform_timeTaylor_minor_ne_zero
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n N : ℕ) (v : Fin N → P)
    (hN : N ≤ n + 1) {K : Set (P × ℝ)} (hK : IsCompact K)
    (hne : ∀ x ∈ K, (timeJetParameterMatrix Φ N v x.2 x.1).det ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, |δ| < ε → ∀ x ∈ K, ∀ τ ∈ Icc (-1 : ℝ) 1,
      (timeJetParameterMatrix (fun y => timeTaylorEval Φ n y.1 x.2 y.2)
        N v (x.2 + δ * τ) x.1).det ≠ 0 := by
  let D : ℝ × ((P × ℝ) × ℝ) → ℝ := fun q =>
    (timeJetParameterMatrix (fun y => timeTaylorEval Φ n y.1 q.2.1.2 y.2)
      N v (q.2.1.2 + q.1 * q.2.2) q.2.1.1).det
  have harg : Continuous (fun q : ℝ × ((P × ℝ) × ℝ) =>
      (q.2.1, q.2.1.2 + q.1 * q.2.2)) := by fun_prop
  have hD : Continuous D :=
    ((continuous_timeTaylorJetParameterMatrix hΦ n N v).comp harg).matrix_det
  let U : Set (ℝ × ((P × ℝ) × ℝ)) := {q | D q ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun hD continuous_const
  have hKU : ({0} : Set ℝ) ×ˢ (K ×ˢ Icc (-1 : ℝ) 1) ⊆ U := by
    rintro ⟨δ, x, τ⟩ ⟨hδ, hx, _⟩
    have hz : δ = 0 := hδ
    subst δ
    change (timeJetParameterMatrix (fun y => timeTaylorEval Φ n y.1 x.2 y.2)
      N v (x.2 + 0 * τ) x.1).det ≠ 0
    rw [zero_mul, add_zero, timeJetParameterMatrix_timeTaylorEval_center Φ n N v _ _ hN]
    exact hne x hx
  obtain ⟨T, V, hT, _, h0T, hKV, hTV⟩ :=
    generalized_tube_lemma isCompact_singleton (hK.prod isCompact_Icc) hU hKU
  have hz : (0 : ℝ) ∈ T := h0T (by simp)
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds hz)
  refine ⟨ε, hε, ?_⟩
  intro δ hδ x hx τ hτ
  have hδball : δ ∈ Metric.ball (0 : ℝ) ε := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hδ
  have hδT : δ ∈ T := hεT hδball
  have hxV : (x, τ) ∈ V := hKV ⟨hx, hτ⟩
  have hpair : (δ, (x, τ)) ∈ U := hTV ⟨hδT, hxV⟩
  exact hpair

/-- The stable determinant also has one strictly positive lower bound
on all sufficiently small closed scales and normalized time slices. -/
theorem exists_uniform_timeTaylor_minor_lower_bound
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n N : ℕ) (v : Fin N → P)
    (hN : N ≤ n + 1) {K : Set (P × ℝ)} (hK : IsCompact K)
    (hne : ∀ x ∈ K, (timeJetParameterMatrix Φ N v x.2 x.1).det ≠ 0) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∀ δ : ℝ, |δ| ≤ ε → ∀ x ∈ K, ∀ τ ∈ Icc (-1 : ℝ) 1,
      b ≤ |(timeJetParameterMatrix (fun y => timeTaylorEval Φ n y.1 x.2 y.2)
        N v (x.2 + δ * τ) x.1).det| := by
  obtain ⟨ε, hε, hne'⟩ := exists_uniform_timeTaylor_minor_ne_zero hΦ n N v hN hK hne
  let D : ℝ × ((P × ℝ) × ℝ) → ℝ := fun q =>
    (timeJetParameterMatrix (fun y => timeTaylorEval Φ n y.1 q.2.1.2 y.2)
      N v (q.2.1.2 + q.1 * q.2.2) q.2.1.1).det
  have harg : Continuous (fun q : ℝ × ((P × ℝ) × ℝ) =>
      (q.2.1, q.2.1.2 + q.1 * q.2.2)) := by fun_prop
  have hD : Continuous D :=
    ((continuous_timeTaylorJetParameterMatrix hΦ n N v).comp harg).matrix_det
  let L : Set (ℝ × ((P × ℝ) × ℝ)) := Icc (-(ε / 2)) (ε / 2) ×ˢ (K ×ˢ Icc (-1 : ℝ) 1)
  have hL : IsCompact L := isCompact_Icc.prod (hK.prod isCompact_Icc)
  have hpos : ∀ q ∈ L, 0 < |D q| := by
    intro q hq
    apply abs_pos.mpr
    have hδ : |q.1| ≤ ε / 2 := abs_le.mpr hq.1
    exact hne' q.1 (hδ.trans_lt (by linarith)) q.2.1 hq.2.1 q.2.2 hq.2.2
  obtain ⟨b, hb, hbound⟩ := hL.exists_forall_le' hD.abs.continuousOn hpos
  refine ⟨ε / 2, b, half_pos hε, hb, ?_⟩
  intro δ hδ x hx τ hτ
  exact hbound (δ, (x, τ)) ⟨abs_le.mp hδ, hx, hτ⟩

end PlanarNikodym
