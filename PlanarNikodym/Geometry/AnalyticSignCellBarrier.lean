import PlanarNikodym.Geometry.AnalyticSeparatingFrontier
import PlanarNikodym.Geometry.SemianalyticCoordinateBalls

/-! Explicit analytic barriers for bounded sign pieces. The product uses
only strict sign tests; equality tests do not make the barrier vanish on
the piece itself. A coordinate box factor kills the artificial boundary. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace PlanarNikodym

def analyticSignBarrier {E I : Type*} [Fintype I]
    (f : I → E → ℝ) (s : I → Fin 3) (x : E) : ℝ :=
  ∏ i : {i // s i ≠ 1}, (f i.val x) ^ 2

theorem analyticSignBarrier_analytic {E I : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : I → E → ℝ) (s : I → Fin 3) {x : E}
    (hf : ∀ i, AnalyticAt ℝ (f i) x) : AnalyticAt ℝ (analyticSignBarrier f s) x := by
  apply Finset.analyticAt_fun_prod
  intro i _
  exact (hf i.val).pow 2

theorem analyticSignBarrier_pos {E I : Type*} [Fintype I]
    (U : Set E) (f : I → E → ℝ) (s : I → Fin 3)
    {x : E} (hx : x ∈ analyticStrongSignCell U f s) :
    0 < analyticSignBarrier f s x := by
  apply Finset.prod_pos
  intro i _
  exact sq_pos_of_ne_zero (polynomialSignCondition_ne_zero i.property (hx.2 i.val))

theorem mem_strongSignCell_of_barrier_ne_zero {E I : Type*} [Fintype I]
    (U : Set E) (f : I → E → ℝ) (s : I → Fin 3) {x : E}
    (hx : x ∈ analyticWeakSignCell U f s) (hn : analyticSignBarrier f s x ≠ 0) :
    x ∈ analyticStrongSignCell U f s := by
  classical
  refine ⟨hx.1, fun i => polynomialSignCondition_strict_of_weak (hx.2 i) ?_⟩
  intro hi hz
  apply hn
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨i, hi⟩ : {i // s i ≠ 1}))
    (by simp only [hz, zero_pow (by decide : 2 ≠ 0)])

def coordinateBoxBarrier {n : ℕ} (c : Fin n → ℝ) (r : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, (r ^ 2 - (x i - c i) ^ 2)

theorem coordinateBoxBarrier_analytic {n : ℕ} (c : Fin n → ℝ) (r : ℝ)
    (x : Fin n → ℝ) : AnalyticAt ℝ (coordinateBoxBarrier c r) x := by
  apply Finset.analyticAt_fun_prod
  intro i _
  exact analyticAt_const.sub
    ((((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).analyticAt x).sub
      analyticAt_const).pow 2)

theorem coordinateBoxBarrier_pos {n : ℕ} (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    {x : Fin n → ℝ} (hx : x ∈ ball c r) : 0 < coordinateBoxBarrier c r x := by
  apply Finset.prod_pos
  intro i _
  have hi := abs_lt.mp (show |x i - c i| < r by
    simpa only [Real.dist_eq] using (dist_pi_lt_iff hr).mp (mem_ball.mp hx) i)
  nlinarith [sq_nonneg (r - (x i - c i)), sq_nonneg (r + (x i - c i))]

theorem mem_ball_of_coordinateBoxBarrier_ne_zero {n : ℕ}
    (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {x : Fin n → ℝ}
    (hx : x ∈ closedBall c r) (hn : coordinateBoxBarrier c r x ≠ 0) : x ∈ ball c r := by
  classical
  rw [mem_ball, dist_pi_lt_iff hr]
  intro i
  have hi : |x i - c i| ≤ r := by
    simpa only [Real.dist_eq] using (dist_pi_le_iff hr.le).mp (mem_closedBall.mp hx) i
  have hne : r ^ 2 - (x i - c i) ^ 2 ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)
  rw [Real.dist_eq]
  apply lt_of_le_of_ne hi
  intro he
  apply hne
  nlinarith [sq_abs (x i - c i)]

/-- A genuine positive analytic function vanishing on every missing
boundary point of the sign piece cut by a relatively compact open box. -/
theorem exists_analytic_sign_piece_barrier
    {n : ℕ} {I : Type*} [Fintype I]
    (U : Set (Fin n → ℝ)) (hU : IsOpen U) (f : I → (Fin n → ℝ) → ℝ)
    (hf : ∀ i, AnalyticOnNhd ℝ (f i) (closure U)) (s : I → Fin 3)
    (c : Fin n → ℝ) (r : ℝ) (hr : 0 < r) (hbox : closedBall c r ⊆ U) :
    ∃ g : (Fin n → ℝ) → ℝ, AnalyticOnNhd ℝ g (closure U) ∧
      (∀ x ∈ analyticStrongSignCell U f s ∩ ball c r, 0 < g x) ∧
      ∀ x ∈ closure (analyticStrongSignCell U f s ∩ ball c r) \
        (analyticStrongSignCell U f s ∩ ball c r), g x = 0 := by
  let g := fun x => analyticSignBarrier f s x * coordinateBoxBarrier c r x
  refine ⟨g, fun x hx => (analyticSignBarrier_analytic f s (fun i => hf i x hx)).mul
    (coordinateBoxBarrier_analytic c r x), ?_, ?_⟩
  · intro x hx
    exact mul_pos (analyticSignBarrier_pos U f s hx.1) (coordinateBoxBarrier_pos c hr hx.2)
  · intro x hx
    by_contra hn
    have hxb : x ∈ closedBall c r :=
      (closure_minimal (fun y hy => ball_subset_closedBall hy.2) isClosed_closedBall) hx.1
    have hxw := closure_analyticStrongSignCell_inter_subset_weak U hU f
      (fun i => ((hf i).mono subset_closure).continuousOn) s ⟨(closure_mono inter_subset_left) hx.1, hbox hxb⟩
    have hparts := mul_ne_zero_iff.mp hn
    exact hx.2 ⟨mem_strongSignCell_of_barrier_ne_zero U f s hxw hparts.1,
      mem_ball_of_coordinateBoxBarrier_ne_zero c hr hxb hparts.2⟩

end PlanarNikodym
