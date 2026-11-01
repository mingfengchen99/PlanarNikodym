import PlanarNikodym.Geometry.FullRankRigidity
import PlanarNikodym.Geometry.AnalyticZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

noncomputable section
open Set Filter Module Function MeasureTheory
open scoped Topology Matrix
namespace PlanarNikodym

/-- Coordinates (z₁,z₂,u₁,…,u_d), with d=0 allowed. -/
def parameterFrame (d : ℕ) : Aux (d + 2) ≃L[ℝ] Parameters 2 d :=
  (show Aux (d + 2) ≃ₗ[ℝ] Parameters 2 d from
    { toFun := fun v => ((fun i => if i = 0 then v 0 else v 1), Fin.tail (Fin.tail v))
      invFun := fun p => Fin.cons (p.1 0) (Fin.cons (p.1 1) p.2)
      left_inv := by
        intro v
        ext i
        refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i <;> rfl
      right_inv := by
        intro p
        apply Prod.ext
        · ext i; fin_cases i <;> simp
        · rfl
      map_add' := by
        intro p q
        apply Prod.ext
        · ext i; fin_cases i <;> simp
        · rfl
      map_smul' := by
        intro s p
        apply Prod.ext
        · ext i; fin_cases i <;> simp
        · rfl }).toContinuousLinearEquiv

/-- Iteration of the actual ambient derivative in the time direction. -/
def timeDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × E → ℝ) : ℕ → ℝ × E → ℝ
  | 0 => f
  | k + 1 => fun x => fderiv ℝ (timeDerivative f k) x (1, 0)

theorem timeDerivative_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ × E → ℝ} {x : ℝ × E} (hf : AnalyticAt ℝ f x) (k : ℕ) :
    AnalyticAt ℝ (timeDerivative f k) x := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    exact ((ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × E)).analyticAt _).comp ih.fderiv

theorem timeDerivative_eq_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ × E → ℝ} (k : ℕ) (x : ℝ × E) (hf : AnalyticAt ℝ f x) :
    timeDerivative f k x = iteratedDeriv k (fun t => f (t, x.2)) x.1 := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have hd := (timeDerivative_analyticAt hf k).differentiableAt
    have hs := fderiv_fst_slice (timeDerivative f k) x hd
    change fderiv ℝ (timeDerivative f k) x (1, 0) = _
    change ((fderiv ℝ (timeDerivative f k) x).comp (ContinuousLinearMap.inl ℝ ℝ E)) 1 = _
    rw [← hs]
    change deriv (fun t => timeDerivative f k (t, x.2)) x.1 = _
    rw [iteratedDeriv_succ]
    apply Filter.EventuallyEq.deriv_eq
    have hc : ContinuousAt (fun t : ℝ => (t, x.2)) x.1 := continuousAt_id.prodMk continuousAt_const
    filter_upwards [hc.preimage_mem_nhds hf.eventually_analyticAt] with t ht
    exact ih (t, x.2) ht

def Family.parameterColumn {d : ℕ} (G : Family 2 d) (j : Fin (d + 2))
    (x : ℝ × Parameters 2 d) : ℝ :=
  fderiv ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x
    (0, parameterFrame d (Pi.single j 1))

def Family.cinematicMatrix {d : ℕ} (G : Family 2 d) (x : ℝ × Parameters 2 d) :
    Matrix (Fin (d + 2)) (Fin (d + 2)) ℝ :=
  fun i j => timeDerivative (G.parameterColumn j) i x

def Family.cinematicDet {d : ℕ} (G : Family 2 d) (x : ℝ × Parameters 2 d) : ℝ :=
  (G.cinematicMatrix x).det

theorem Family.parameterColumn_analyticAt {d : ℕ} (G : Family 2 d)
    {x : ℝ × Parameters 2 d} (ha : AnalyticAt ℝ (fun y => G.γ y.1 y.2) x)
    (j : Fin (d + 2)) : AnalyticAt ℝ (G.parameterColumn j) x :=
  ((ContinuousLinearMap.apply ℝ ℝ
    ((0, parameterFrame d (Pi.single j 1)) : ℝ × Parameters 2 d)).analyticAt _).comp ha.fderiv

theorem Family.cinematicDet_analytic {d : ℕ} (G : Family 2 d) (ha : G.IsAnalytic) :
    AnalyticOnNhd ℝ G.cinematicDet (G.I.carrier ×ˢ G.W) := by
  intro x hx
  apply analyticAt_det
  intro i j
  exact timeDerivative_analyticAt (G.parameterColumn_analyticAt (ha x hx) j) i

def wronskian {n : ℕ} (f : Fin n → ℝ → ℝ) (t : ℝ) : ℝ :=
  Matrix.det (fun i j : Fin n => iteratedDeriv i (f j) t)

/-- The analytic Wronskian statement used in P5. P8 supplies the theorem
`bocher_input` in Bocher. Earlier interfaces retain the explicit proof
parameter for compatibility; it is no longer an unproved dependency. -/
def BocherInput : Prop :=
  ∀ (n : ℕ) (I : Interval) (f : Fin n → ℝ → ℝ),
    (∀ j, AnalyticOnNhd ℝ (f j) I.carrier) →
    LinearIndependent ℝ (fun j (t : I.carrier) => f j t) →
    ∃ t ∈ I.carrier, wronskian f t ≠ 0

theorem full_curve_rank_cinematic_nonzero (hB : BocherInput) {d : ℕ} (G : Family 2 d)
    (ha : G.IsAnalytic) (p : Parameters 2 d) (hp : p ∈ G.W)
    (hc : G.curveRank p = d + 2) : ∃ t ∈ G.I.carrier, G.cinematicDet (t, p) ≠ 0 := by
  let f : Fin (d + 2) → ℝ → ℝ := fun j t => G.parameterColumn j (t, p)
  have hfa : ∀ j, AnalyticOnNhd ℝ (f j) G.I.carrier := by
    intro j t ht
    exact (G.parameterColumn_analyticAt (ha (t, p) ⟨ht, hp⟩) j).comp
      (f := fun t : ℝ => (t, p)) (analyticAt_id.prod analyticAt_const)
  let L := functionDerivative (fun (t : G.I.carrier) => G.γ t) p
  have hr : finrank ℝ L.range = finrank ℝ (Parameters 2 d) := by
    rw [← G.curveSpace_eq_range p (fun t => (G.parameter_analytic ha p hp t).differentiableAt)]
    simpa only [Module.finrank_prod, Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      mul_one, Nat.add_comm] using (show finrank ℝ (G.curveSpace p) = d + 2 from hc)
  have hk := L.finrank_range_add_finrank_ker
  have hi : Injective L := LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp (by omega))
  let A : Aux (d + 2) →ₗ[ℝ] (G.I.carrier → ℝ) := L.comp (parameterFrame d).toLinearMap
  have hai : Injective A := hi.comp (parameterFrame d).injective
  have hli := (Pi.basisFun ℝ (Fin (d + 2))).linearIndependent.map' A
    (LinearMap.ker_eq_bot.mpr hai)
  have hcol (j : Fin (d + 2)) (t : G.I.carrier) :
      f j t = A (Pi.single j 1) t := by
    have he := fderiv_snd_slice (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2)
      ((t : ℝ), p) (ha (t, p) ⟨t.property, hp⟩).differentiableAt
    exact (congrArg (fun M : Parameters 2 d →L[ℝ] ℝ => M
      (parameterFrame d (Pi.single j 1))) he).symm
  have hfli : LinearIndependent ℝ (fun j (t : G.I.carrier) => f j t) := by
    have he : (fun j (t : G.I.carrier) => f j t) = fun j => A (Pi.single j 1) := by
      ext j t; exact hcol j t
    rw [he]
    simpa only [Function.comp_def, Pi.basisFun_apply] using hli
  obtain ⟨t, ht, hn⟩ := hB (d + 2) G.I f hfa hfli
  refine ⟨t, ht, ?_⟩
  have he : G.cinematicDet (t, p) = wronskian f t := by
    unfold Family.cinematicDet wronskian
    apply congrArg Matrix.det
    funext i j
    exact timeDerivative_eq_iteratedDeriv i (t, p)
      (G.parameterColumn_analyticAt (ha (t, p) ⟨ht, hp⟩) j)
  rwa [he]

theorem full_curve_rank_cinematic_exceptions_finite (hB : BocherInput) {d : ℕ}
    (G : Family 2 d) (ha : G.IsAnalytic) (p : Parameters 2 d) (hp : p ∈ G.W)
    (hc : G.curveRank p = d + 2) :
    {t | t ∈ G.I.carrier ∧ G.cinematicDet (t, p) = 0}.Finite := by
  apply analytic_zeros_finite_interval G.I
  · intro t ht
    exact (G.cinematicDet_analytic ha (t, p) ⟨ht, hp⟩).comp
      (f := fun t : ℝ => (t, p)) (analyticAt_id.prod analyticAt_const)
  · exact full_curve_rank_cinematic_nonzero hB G ha p hp hc

end PlanarNikodym
