import PlanarNikodym.Rank.Bocher

noncomputable section
open Set Filter Submodule
open scoped Topology Matrix
namespace PlanarNikodym

theorem independent_of_wronskian_ne_zero_interior {n : ℕ} (I : Interval)
    (f : Fin n → ℝ → ℝ) (hf : ∀ j, AnalyticOnNhd ℝ (f j) I.carrier)
    (q : ℝ) (hq : q ∈ Ioo I.left I.right) (hW : wronskian f q ≠ 0) :
    LinearIndependent ℝ (fun j (t : I.carrier) => f j t) := by
  classical
  have hqI : q ∈ I.carrier := ⟨hq.1.le, hq.2.le⟩
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hzero : (fun x => ∑ j, c j * f j x) =ᶠ[𝓝 q] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hq] with x hx
    have he := congrFun hc (⟨x, hx.1.le, hx.2.le⟩ : I.carrier)
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he
  have hjet (i : Fin n) : ∑ j, c j * iteratedDeriv i (f j) q = 0 := by
    have hd := hzero.iteratedDeriv_eq i.val
    rw [iteratedDeriv_fun_sum (f := fun j x => c j * f j x) (I := Finset.univ)
      (fun j _ => (analyticAt_const.mul (hf j q hqI)).contDiffAt)] at hd
    simpa [iteratedDeriv_const_mul_field, iteratedDeriv_const] using hd
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => iteratedDeriv i (f j) q
  have hi : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hW))
  have hz : A *ᵥ c = A *ᵥ 0 := by
    ext i
    simpa [A, Matrix.mulVec, dotProduct, mul_comm] using hjet i
  exact fun j => congrFun (hi hz) j

/-- Moving a nonzero value off the endpoints only uses continuity. -/
theorem exists_interior_ne_zero (I : Interval) (F : ℝ → ℝ)
    (hF : ∀ x ∈ I.carrier, ContinuousAt F x)
    (hne : ∃ x ∈ I.carrier, F x ≠ 0) :
    ∃ x ∈ Ioo I.left I.right, F x ≠ 0 := by
  obtain ⟨x, hx, hnx⟩ := hne
  have hcl : x ∈ closure (Ioo I.left I.right) := by
    rw [closure_Ioo I.nondegenerate.ne]
    exact hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ((hF x hx).eventually_ne hnx)
  obtain ⟨y, hyB, hyI⟩ := _root_.mem_closure_iff.mp hcl (Metric.ball x r)
    Metric.isOpen_ball (Metric.mem_ball_self hr)
  exact ⟨y, hyI, hball hyB⟩

/-- The full equivalence in Theorem 5.3 for the project's nondegenerate
closed intervals, including both endpoints and the empty family. -/
theorem theorem_5_3 (n : ℕ) (I : Interval) (f : Fin n → ℝ → ℝ)
    (hf : ∀ j, AnalyticOnNhd ℝ (f j) I.carrier) :
    (¬ LinearIndependent ℝ (fun j (t : I.carrier) => f j t)) ↔
      ∀ t ∈ I.carrier, wronskian f t = 0 := by
  constructor
  · intro hnot t ht
    by_contra hn
    obtain ⟨q, hq, hqW⟩ := exists_interior_ne_zero I (wronskian f)
      (fun x hx => (wronskian_analytic f I.carrier hf x hx).continuousAt) ⟨t, ht, hn⟩
    exact hnot (independent_of_wronskian_ne_zero_interior I f hf q hq hqW)
  · intro hzero hli
    obtain ⟨t, ht, hn⟩ := bocher_input n I f hf hli
    exact hn (hzero t ht)

end PlanarNikodym
