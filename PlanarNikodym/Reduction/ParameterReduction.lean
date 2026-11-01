import PlanarNikodym.Geometry.LocalCoordinates
import PlanarNikodym.Geometry.AnalyticImplicit
import PlanarNikodym.Core.Definitions

noncomputable section
open Set Filter Submodule Module
open scoped Topology ContDiff Matrix
namespace PlanarNikodym

abbrev BlockParameters (a b c : ℕ) := (Aux a × Aux b) × Aux c

def wIn (a b c : ℕ) : Aux b →L[ℝ] BlockParameters a b c :=
  (ContinuousLinearMap.inl ℝ (Aux a × Aux b) (Aux c)).comp
    (ContinuousLinearMap.inr ℝ (Aux a) (Aux b))

def etaIn (a b c : ℕ) : Aux c →L[ℝ] BlockParameters a b c :=
  ContinuousLinearMap.inr ℝ (Aux a × Aux b) (Aux c)

def wDerivative {X : Type*} {a b c : ℕ} (φ : X → BlockParameters a b c → ℝ)
    (p : BlockParameters a b c) : Aux b →ₗ[ℝ] (X → ℝ) :=
  (functionDerivative φ p).comp (wIn a b c).toLinearMap

def etaDerivative {X : Type*} {a b c : ℕ} (φ : X → BlockParameters a b c → ℝ)
    (p : BlockParameters a b c) : Aux c →ₗ[ℝ] (X → ℝ) :=
  (functionDerivative φ p).comp (etaIn a b c).toLinearMap

def BlockRank {X : Type*} {a b c : ℕ} (φ : X → BlockParameters a b c → ℝ)
    (p : BlockParameters a b c) : Prop :=
  finrank ℝ (wDerivative φ p).range = b ∧
    finrank ℝ ((wDerivative φ p).range ⊔ (etaDerivative φ p).range : Submodule ℝ (X → ℝ)) = b

theorem block_rank_range_le {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (p : BlockParameters a b c)
    (h : BlockRank φ p) : (etaDerivative φ p).range ≤ (wDerivative φ p).range := by
  have heq : (wDerivative φ p).range = (wDerivative φ p).range ⊔ (etaDerivative φ p).range :=
    Submodule.eq_of_le_of_finrank_eq le_sup_left (h.1.trans h.2.symm)
  rw [heq]
  exact le_sup_right

theorem block_direction_mem {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (p k : BlockParameters a b c)
    (hr : BlockRank φ p) (hk : k.1.1 = 0) :
    functionDerivative φ p k ∈ (wDerivative φ p).range := by
  have heq : k = wIn a b c k.1.2 + etaIn a b c k.2 := by
    ext <;> simp [wIn, etaIn, hk]
  rw [heq, map_add]
  apply Submodule.add_mem
  · exact ⟨k.1.2, rfl⟩
  · exact block_rank_range_le φ p hr ⟨k.2, rfl⟩

theorem block_eval_kernel {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (p k : BlockParameters a b c)
    (hr : BlockRank φ p) (x : Fin b → X)
    (hdet : Matrix.det (fun i j => wDerivative φ p (Pi.single j 1) (x i)) ≠ 0)
    (hk : k.1.1 = 0) (hz : ∀ i, fderiv ℝ (φ (x i)) p k = 0) :
    ∀ t, fderiv ℝ (φ t) p k = 0 := by
  have hm := block_direction_mem φ p k hr hk
  rw [range_eq_span_coordinates] at hm
  have heq := eq_zero_of_mem_span_of_eval_zero
    (fun j => wDerivative φ p (Pi.single j 1)) x hdet
    (functionDerivative φ p k) hm hz
  exact fun t => congrFun heq t

def compensated {a b c : ℕ} (κ : BlockParameters a b c → Aux b)
    (p : BlockParameters a b c) : BlockParameters a b c := ((p.1.1, κ p), p.2)

theorem hasFDerivAt_wInsert {a b c : ℕ} (p : BlockParameters a b c) :
    HasFDerivAt (fun w : Aux b => ((p.1.1, w), p.2)) (wIn a b c) p.1.2 := by
  convert ((hasFDerivAt_const (𝕜 := ℝ) p.1.1 p.1.2).prodMk
    (hasFDerivAt_id (𝕜 := ℝ) p.1.2)).prodMk
    (hasFDerivAt_const (𝕜 := ℝ) p.2 p.1.2) using 1 <;> rfl

def evalWDerivative {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (x : Fin b → X) (p : BlockParameters a b c) :
    Aux b →L[ℝ] Aux b :=
  ContinuousLinearMap.pi (fun i => (fderiv ℝ (φ (x i)) p).comp (wIn a b c))

theorem evalWDerivative_isInvertible {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (x : Fin b → X) (p : BlockParameters a b c)
    (hdet : Matrix.det (fun i j => wDerivative φ p (Pi.single j 1) (x i)) ≠ 0) :
    (evalWDerivative φ x p).IsInvertible := isInvertible_of_det_coordinates _ hdet

theorem hasFDerivAt_evalWSlice {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (x : Fin b → X) (p : BlockParameters a b c)
    (hf : ∀ i, DifferentiableAt ℝ (φ (x i)) p) :
    HasFDerivAt (fun w : Aux b => fun i => φ (x i) ((p.1.1, w), p.2))
      (evalWDerivative φ x p) p.1.2 := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (hf i).hasFDerivAt.comp _ (hasFDerivAt_wInsert p)

/-- The finite evaluation equations solved by the analytic implicit theorem. -/
def compensationEquation {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (x : Fin b → X) (η₀ : Aux c)
    (z : BlockParameters a b c × Aux b) : Aux b :=
  fun i => φ (x i) ((z.1.1.1, z.2), z.1.2) - φ (x i) (z.1.1, η₀)

theorem compensationEquation_analyticAt {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (x : Fin b → X) (q : BlockParameters a b c)
    (hf : ∀ i, AnalyticAt ℝ (φ (x i)) q) :
    AnalyticAt ℝ (compensationEquation φ x q.2) (q, q.1.2) := by
  apply AnalyticAt.pi
  intro i
  have hleft : AnalyticAt ℝ (fun z : BlockParameters a b c × Aux b =>
      ((z.1.1.1, z.2), z.1.2)) (q, q.1.2) :=
    ((analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)).prod analyticAt_snd).prod
      (analyticAt_snd.comp analyticAt_fst)
  have hright : AnalyticAt ℝ (fun z : BlockParameters a b c × Aux b =>
      (z.1.1, q.2)) (q, q.1.2) :=
    (analyticAt_fst.comp analyticAt_fst).prod analyticAt_const
  exact ((hf i).comp hleft).sub ((hf i).comp hright)

theorem compensationEquation_partial {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (x : Fin b → X) (q : BlockParameters a b c)
    (hf : ∀ i, AnalyticAt ℝ (φ (x i)) q) :
    (fderiv ℝ (compensationEquation φ x q.2) (q, q.1.2)).comp
      (ContinuousLinearMap.inr ℝ (BlockParameters a b c) (Aux b)) = evalWDerivative φ x q := by
  rw [← fderiv_snd_slice _ _ (compensationEquation_analyticAt φ x q hf).differentiableAt]
  have h := (hasFDerivAt_evalWSlice φ x q (fun i => (hf i).differentiableAt)).sub_const
    (fun i => φ (x i) q)
  exact h.fderiv

theorem exists_compensator {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (q : BlockParameters a b c)
    (hf : ∀ t, AnalyticAt ℝ (φ t) q) (hr : BlockRank φ q) :
    ∃ x : Fin b → X, ∃ κ : BlockParameters a b c → Aux b,
      AnalyticAt ℝ κ q ∧ κ q = q.1.2 ∧
      (∀ᶠ p in 𝓝 q, ∀ i, φ (x i) (compensated κ p) = φ (x i) (p.1, q.2)) ∧
      (∀ᶠ v in 𝓝 q.1, κ (v, q.2) = v.2) ∧
      Matrix.det (fun i j => wDerivative φ q (Pi.single j 1) (x i)) ≠ 0 := by
  have hli := independent_of_rank_eq (fun j => wDerivative φ q (Pi.single j 1))
    (by rw [← range_eq_span_coordinates]; exact hr.1)
  obtain ⟨x, hx⟩ := exists_eval_det_ne_zero _ hli
  have hi := evalWDerivative_isInvertible φ x q hx
  rw [← compensationEquation_partial φ x q (fun i => hf (x i))] at hi
  obtain ⟨κ, hκ, hκq, hEq, hUnique⟩ := exists_analytic_implicit
    (compensationEquation φ x q.2) q q.1.2
    (compensationEquation_analyticAt φ x q (fun i => hf (x i)))
    (by ext i; simp [compensationEquation]) hi
  refine ⟨x, κ, hκ, hκq, ?_, ?_, hx⟩
  · filter_upwards [hEq] with p hp i
    exact sub_eq_zero.mp (congrFun hp i)
  · have ht : Tendsto (fun v : Aux a × Aux b => ((v, q.2), v.2)) (𝓝 q.1) (𝓝 (q, q.1.2)) := by
      convert (continuousAt_id.prodMk continuousAt_const).prodMk continuousAt_snd using 1 <;> rfl
    filter_upwards [ht hUnique] with v hv
    apply hv.mp
    ext i
    simp [compensationEquation]

end PlanarNikodym
