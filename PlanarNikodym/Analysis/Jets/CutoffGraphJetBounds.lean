import PlanarNikodym.Analysis.Jets.JetAmplitudeExpansion

/-! Actual uniform bounds for the geometry and cutoff jets on the cutoff
support. Only pointwise smoothness at that support is required. -/
noncomputable section
open Set
open scoped ContDiff
universe u

namespace PlanarNikodym

/-- Joint local smoothness of the actual partial derivative, allowing any
normed frozen parameter space. -/
theorem contDiffAt_fiber_fderiv
    {P Q E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : P × Q → E} {x : P × Q} (hH : ContDiffAt ℝ ∞ H x) :
    ContDiffAt ℝ ∞ (fun y : P × Q => fderiv ℝ (fun p => H (p, y.2)) y.1) x := by
  have hdup : ContDiffAt ℝ ∞
      (Function.uncurry (fun y : P × Q => fun p : P => H (p, y.2))) (x, x.1) :=
    hH.comp (x, x.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact hdup.fderiv contDiffAt_fst (by simp)

/-- The complete fiber jet is locally smooth as a function of both the
fiber and the frozen variables. No derivative regularity is postulated. -/
theorem contDiffAt_fiber_iteratedFDeriv (j : ℕ)
    {P Q E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : P × Q → E} {x : P × Q} (hH : ContDiffAt ℝ ∞ H x) :
    ContDiffAt ℝ ∞ (fun y : P × Q => iteratedFDeriv ℝ j (fun p => H (p, y.2)) y.1) x := by
  induction j generalizing E with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ P E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x hH
  | succ j ih =>
    let D : P × Q → P →L[ℝ] E := fun y => fderiv ℝ (fun p => H (p, y.2)) y.1
    let C := (continuousMultilinearCurryRightEquiv' ℝ j P E).symm.toContinuousLinearEquiv
    have heq : (fun y : P × Q => iteratedFDeriv ℝ (j + 1) (fun p => H (p, y.2)) y.1) =
        fun y => C (iteratedFDeriv ℝ j (fun p => D (p, y.2)) y.1) := by
      funext y
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq]
    exact C.contDiff.contDiffAt.comp x (ih (contDiffAt_fiber_fderiv hH))

def Family.cutoffGraphJet {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (j : ℕ) (x : ℝ × Parameters 2 d) : Aux d [×j]→L[ℝ] (ℂ × Plane) :=
  iteratedFDeriv ℝ j (G.cutoffGraphMap χ x.2.1 x.1) x.2.2

/-- Geometry jets are jointly continuous on the actual cutoff support,
even when the chosen geometric extension is irregular elsewhere. -/
theorem Family.continuousOn_cutoffGraphJet {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x) (j : ℕ) :
    ContinuousOn (G.cutoffGraphJet χ j) (tsupport χ) := by
  intro x hx
  let R : (Aux d × (ℝ × Base 2)) → ℝ × Parameters 2 d :=
    fun y => (y.2.1, (y.2.2, y.1))
  let T : (ℝ × Parameters 2 d) → Aux d × (ℝ × Base 2) :=
    fun y => (y.2.2, (y.1, y.2.1))
  let H : (Aux d × (ℝ × Base 2)) → ℂ × Plane := fun y =>
    ((χ (R y) : ℂ), ((R y).1, G.γ (R y).1 (R y).2))
  have hR : ContDiff ℝ ∞ R := contDiff_snd.fst.prodMk (contDiff_snd.snd.prodMk contDiff_fst)
  have hH : ContDiffAt ℝ ∞ H (T x) := by
    exact ((Complex.ofRealCLM.contDiff.comp (hχ.comp hR)).contDiffAt).prodMk
      ((hR.contDiffAt.fst).prodMk ((hγ x hx).comp (f := R) (T x) hR.contDiffAt))
  have hJ := (contDiffAt_fiber_iteratedFDeriv j hH).continuousAt
  have hT : Continuous T := continuous_snd.snd.prodMk (continuous_fst.prodMk continuous_snd.fst)
  exact (hJ.comp hT.continuousAt).continuousWithinAt

/-- An actual finite positive bound, uniform in the support point and in
all orders up to `s`. It depends only on geometry, cutoff and `s`. -/
theorem Family.exists_uniform_cutoffGraphJet_bound {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x) (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ s, ∀ x ∈ tsupport χ, ‖G.cutoffGraphJet χ j x‖ ≤ C := by
  have hb (j : ℕ) : ∃ C : ℝ, ∀ x ∈ tsupport χ, ‖G.cutoffGraphJet χ j x‖ ≤ C :=
    hc.isCompact.exists_bound_of_continuousOn (G.continuousOn_cutoffGraphJet χ hχ hγ j)
  choose B hB using hb
  let C : ℝ := 1 + ∑ j ∈ Finset.range (s + 1), |B j|
  refine ⟨C, ?_, ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => abs_nonneg (B i)))
  intro j hj x hx
  apply (hB j x hx).trans
  have hsum : |B j| ≤ ∑ i ∈ Finset.range (s + 1), |B i| :=
    Finset.single_le_sum (fun i _ => abs_nonneg (B i)) (by simpa using hj)
  dsimp [C]
  linarith [le_abs_self (B j)]

end PlanarNikodym
