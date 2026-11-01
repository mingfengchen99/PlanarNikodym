import PlanarNikodym.Rank.WronskianAlgebra

noncomputable section
open Set Filter Submodule
open scoped Topology Matrix
namespace PlanarNikodym

/-- Differentiating all rows of a local jet relation forces the
coefficients to be constant wherever the initial Wronskian is invertible. -/
theorem local_jet_coefficients_deriv_zero {n : ℕ}
    (f : Fin (n + 1) → ℝ → ℝ) (C : Fin n → ℝ → ℝ) (U : Set ℝ)
    (hU : IsOpen U) (hf : ∀ j, AnalyticOnNhd ℝ (f j) U)
    (hC : ∀ j, AnalyticOnNhd ℝ (C j) U)
    (hW : ∀ x ∈ U, wronskian (fun j : Fin n => f j.castSucc) x ≠ 0)
    (he : ∀ x ∈ U, ∀ i : Fin (n + 1),
      iteratedDeriv i (f (Fin.last n)) x =
        ∑ j : Fin n, C j x * iteratedDeriv i (f j.castSucc) x) :
    ∀ x ∈ U, ∀ j, deriv (C j) x = 0 := by
  classical
  intro x hx
  apply coefficient_derivatives_zero _ C x (hW x hx)
  intro i
  have hi (j : Fin (n + 1)) :
      HasDerivAt (iteratedDeriv i.val (f j)) (iteratedDeriv (i.val + 1) (f j) x) x := by
    rw [iteratedDeriv_succ]
    exact (analyticAt_iteratedDeriv_real (hf j x hx) i).differentiableAt.hasDerivAt
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun j (_ : j ∈ Finset.univ) =>
    ((hC j x hx).differentiableAt.hasDerivAt).mul (hi j.castSucc))
  simp only [Pi.mul_apply] at hd
  have hevent : (iteratedDeriv i.val (f (Fin.last n))) =ᶠ[𝓝 x]
      (fun y => ∑ j : Fin n, C j y * iteratedDeriv i.val (f j.castSucc) y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact he y hy i.castSucc
  have hdiff := hevent.deriv_eq
  rw [← iteratedDeriv_succ, hd.deriv] at hdiff
  have hnext := he x hx ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  change iteratedDeriv (i.val + 1) (f (Fin.last n)) x =
    ∑ j : Fin n, C j x * iteratedDeriv (i.val + 1) (f j.castSucc) x at hnext
  rw [Finset.sum_add_distrib] at hdiff
  linarith

/-- Bôcher's theorem, in the direction used by the classification, with
the nonzero point in the interior. No Wronskian or ODE theorem is assumed. -/
theorem bocher_interior (n : ℕ) (I : Interval) (f : Fin n → ℝ → ℝ)
    (hf : ∀ j, AnalyticOnNhd ℝ (f j) I.carrier)
    (hli : LinearIndependent ℝ (fun j (t : I.carrier) => f j t)) :
    ∃ t ∈ Ioo I.left I.right, wronskian f t ≠ 0 := by
  classical
  induction n with
  | zero =>
    refine ⟨(I.left + I.right) / 2, ⟨by linarith [I.nondegenerate],
      by linarith [I.nondegenerate]⟩, ?_⟩
    simp [wronskian]
  | succ n ih =>
    let g : Fin n → ℝ → ℝ := fun j => f j.castSucc
    have hgli : LinearIndependent ℝ (fun j (t : I.carrier) => g j t) :=
      (linearIndependent_finSucc'.mp hli).1
    obtain ⟨q, hq, hqW⟩ := ih g (fun j => hf j.castSucc) hgli
    by_contra hnot
    have hzero : ∀ x ∈ Ioo I.left I.right, wronskian f x = 0 := by
      intro x hx
      by_contra hn
      exact hnot ⟨x, hx, hn⟩
    let W := {x | x ∈ Ioo I.left I.right ∧ wronskian g x ≠ 0}
    have hqI : q ∈ I.carrier := ⟨hq.1.le, hq.2.le⟩
    have hWnhds : W ∈ 𝓝 q := inter_mem (isOpen_Ioo.mem_nhds hq)
      ((wronskian_analytic g I.carrier (fun j => hf j.castSucc) q hqI).continuousAt.eventually_ne hqW)
    let F : Fin n → Fin (n + 1) → ℝ → ℝ :=
      fun j i x => iteratedDeriv i (f j.castSucc) x
    let H : Fin (n + 1) → ℝ → ℝ := fun i x => iteratedDeriv i (f (Fin.last n)) x
    have hF : ∀ j i, AnalyticOnNhd ℝ (F j i) W := by
      intro j i x hx
      exact analyticAt_iteratedDeriv_real (hf j.castSucc x ⟨hx.1.1.le, hx.1.2.le⟩) i
    have hH : ∀ i, AnalyticOnNhd ℝ (H i) W := by
      intro i x hx
      exact analyticAt_iteratedDeriv_real (hf (Fin.last n) x ⟨hx.1.1.le, hx.1.2.le⟩) i
    have hFli : LinearIndependent ℝ (fun j i => F j i q) :=
      independent_of_eval_det_ne_zero _ (fun i => i.castSucc) hqW
    have hspan : ∀ x ∈ W, (fun i => H i x) ∈ span ℝ (range (fun j i => F j i x)) := by
      intro x hx
      exact last_column_mem_span_of_singular (fun i j => iteratedDeriv i (f j) x)
        hx.2 (hzero x hx.1)
    obtain ⟨U, hU, hqU, hUW, C, hC, he⟩ :=
      analytic_coefficients_of_mem_span F H W q hWnhds hF hH hFli hspan
    have hderiv : ∀ x ∈ U, ∀ j, deriv (C j) x = 0 :=
      local_jet_coefficients_deriv_zero f C U hU
        (fun j x hx => hf j x ⟨(hUW hx).1.1.le, (hUW hx).1.2.le⟩)
        hC (fun x hx => (hUW hx).2) he
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hqU)
    have hqB : q ∈ Metric.ball q r := Metric.mem_ball_self hr
    have hconst (j : Fin n) {x : ℝ} (hx : x ∈ Metric.ball q r) : C j x = C j q :=
      Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball q r).isPreconnected
        (fun y hy => (hC j y (hrU hy)).differentiableAt.differentiableWithinAt)
        (fun y hy => hderiv y (hrU hy) j) hx hqB
    have hlocal : f (Fin.last n) =ᶠ[𝓝 q] (fun x => ∑ j : Fin n, C j q * f j.castSucc x) := by
      filter_upwards [Metric.ball_mem_nhds q hr] with x hx
      have h := he x (hrU hx) 0
      change f (Fin.last n) x = ∑ j : Fin n, C j x * f j.castSucc x at h
      have heC : ∀ j, C j x = C j q := fun j => hconst j hx
      simpa only [heC] using h
    have hsum : AnalyticOnNhd ℝ (fun x => ∑ j : Fin n, C j q * f j.castSucc x) I.carrier := by
      intro x hx
      exact Finset.analyticAt_fun_sum _ (fun j _ => analyticAt_const.mul (hf j.castSucc x hx))
    have hglobal := (hf (Fin.last n)).eqOn_of_preconnected_of_eventuallyEq hsum
      isPreconnected_Icc hqI hlocal
    apply (linearIndependent_finSucc'.mp hli).2
    apply (mem_span_range_iff_exists_fun ℝ).mpr
    refine ⟨fun j => C j q, ?_⟩
    ext t
    simpa [Fin.init, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (hglobal t.property).symm

/-- The formerly unproved P5/P7 input is now supplied by a Lean proof. -/
theorem bocher_input : BocherInput := by
  intro n I f hf hli
  obtain ⟨t, ht, hn⟩ := bocher_interior n I f hf hli
  exact ⟨t, ⟨ht.1.le, ht.2.le⟩, hn⟩

end PlanarNikodym
