import PlanarNikodym.Rank.FiniteEvaluation
import Mathlib.Analysis.Analytic.Constructions

noncomputable section
open Set Filter Submodule
open scoped Topology Matrix
namespace PlanarNikodym

/-- Determinants are analytic when their entries are analytic. -/
theorem analyticAt_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {A : E → Matrix (Fin m) (Fin m) ℝ} {q : E}
    (hA : ∀ i j, AnalyticAt ℝ (fun w => A w i j) q) :
    AnalyticAt ℝ (fun w => (A w).det) q := by
  classical
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  exact Finset.analyticAt_fun_prod _ (fun i _ => hA _ _)

/-- Analytic Cramer coefficients, as a quotient of determinants. -/
def cramerCoefficient {E : Type*} {m : ℕ} (A : E → Matrix (Fin m) (Fin m) ℝ)
    (b : E → Fin m → ℝ) (j : Fin m) (w : E) : ℝ :=
  ((A w).updateCol j (b w)).det / (A w).det

theorem analyticAt_cramerCoefficient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {A : E → Matrix (Fin m) (Fin m) ℝ} {b : E → Fin m → ℝ} {q : E}
    (hA : ∀ i j, AnalyticAt ℝ (fun w => A w i j) q)
    (hb : ∀ i, AnalyticAt ℝ (fun w => b w i) q)
    (hne : (A q).det ≠ 0) (j : Fin m) :
    AnalyticAt ℝ (cramerCoefficient A b j) q := by
  classical
  apply (analyticAt_det (A := fun w => (A w).updateCol j (b w)) ?_).div
    (analyticAt_det hA) hne
  intro i k
  by_cases hk : k = j
  · subst k
    simpa using hb i
  · simpa [Matrix.updateCol, hk] using hA i k

/-- If g lies in the span, Cramer's coefficients recover g at every point. -/
theorem cramer_represents {X : Type*} {m : ℕ} (f : Fin m → X → ℝ) (g : X → ℝ)
    (x : Fin m → X) (hne : Matrix.det (fun i j => f j (x i)) ≠ 0)
    (hg : g ∈ span ℝ (range f)) :
    ∀ t, g t = ∑ j, cramerCoefficient (fun _ : Unit => fun i j => f j (x i))
      (fun _ : Unit => fun i => g (x i)) j () * f j t := by
  classical
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℝ).mp hg
  have hcf : ∀ t, ∑ j, c j * f j t = g t := by
    intro t
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hc t
  let A : Matrix (Fin m) (Fin m) ℝ := fun i j => f j (x i)
  have hb : (fun i => g (x i)) = A *ᵥ c := by
    funext i
    simpa [Matrix.mulVec, dotProduct, A, mul_comm] using (hcf (x i)).symm
  have hC : ∀ j, cramerCoefficient (fun _ : Unit => A)
      (fun _ : Unit => fun i => g (x i)) j () = c j := by
    intro j
    rw [cramerCoefficient, hb]
    change (A.cramer (A *ᵥ c)) j / A.det = c j
    have hcA : A.cramer (A *ᵥ c) = A.det • c := by
      rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
        Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hcA]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_div_cancel_left₀ (c j) hne
  intro t
  change g t = ∑ j, cramerCoefficient (fun _ : Unit => A)
    (fun _ : Unit => fun i => g (x i)) j () * f j t
  simpa only [hC] using (hcf t).symm

/-- Local analytic dependence of coefficients. This form requires only analytic
parameter slices and pointwise span membership near q, weaker than Lemma 5.6. -/
theorem analytic_coefficients_of_mem_span {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (f : Fin m → X → E → ℝ) (g : X → E → ℝ) (W : Set E) (q : E)
    (hW : W ∈ 𝓝 q)
    (hf : ∀ j t, AnalyticOnNhd ℝ (f j t) W)
    (hg : ∀ t, AnalyticOnNhd ℝ (g t) W)
    (hli : LinearIndependent ℝ (fun j t => f j t q))
    (hspan : ∀ w ∈ W, (fun t => g t w) ∈ span ℝ (range (fun j t => f j t w))) :
    ∃ U : Set E, IsOpen U ∧ q ∈ U ∧ U ⊆ W ∧
      ∃ C : Fin m → E → ℝ, (∀ j, AnalyticOnNhd ℝ (C j) U) ∧
        ∀ w ∈ U, ∀ t, g t w = ∑ j, C j w * f j t w := by
  classical
  obtain ⟨x, hx⟩ := exists_eval_det_ne_zero _ hli
  let A : E → Matrix (Fin m) (Fin m) ℝ := fun w i j => f j (x i) w
  let b : E → Fin m → ℝ := fun w i => g (x i) w
  have hqW : q ∈ W := mem_of_mem_nhds hW
  have hdet : AnalyticAt ℝ (fun w => (A w).det) q :=
    analyticAt_det (fun i j => hf j (x i) q hqW)
  have hn : ∀ᶠ w in 𝓝 q, (A w).det ≠ 0 :=
    hdet.continuousAt.eventually_ne hx
  obtain ⟨U, hUsub, hUopen, hqU⟩ := mem_nhds_iff.mp (inter_mem hW hn)
  refine ⟨U, hUopen, hqU, fun w hw => (hUsub hw).1,
    cramerCoefficient A b, ?_, ?_⟩
  · intro j w hw
    exact analyticAt_cramerCoefficient
      (fun i k => hf k (x i) w (hUsub hw).1)
      (fun i => hg (x i) w (hUsub hw).1) (hUsub hw).2 j
  · intro w hw t
    exact cramer_represents (fun j t => f j t w) (fun t => g t w) x
      (hUsub hw).2 (hspan w (hUsub hw).1) t

end PlanarNikodym
