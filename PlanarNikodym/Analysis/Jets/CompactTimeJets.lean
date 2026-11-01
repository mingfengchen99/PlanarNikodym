import PlanarNikodym.Analysis.Jets.CompactTimeDerivative

/-! Every finite parameter jet commutes with integration over a fixed
compact time support. These are actual multilinear Fréchet derivatives. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
universe u

namespace PlanarNikodym

theorem contDiff_parameter_iteratedFDeriv (j : ℕ)
    {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : P × ℝ → E} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun x : P × ℝ => iteratedFDeriv ℝ j (fun p => H (p, x.2)) x.1) := by
  induction j generalizing E with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ P E).symm.toContinuousLinearEquiv.contDiff.comp hH
  | succ j ih =>
    let D : P × ℝ → P →L[ℝ] E := fun x => fderiv ℝ (fun p => H (p, x.2)) x.1
    let C := (continuousMultilinearCurryRightEquiv' ℝ j P E).symm.toContinuousLinearEquiv
    have heq : (fun x : P × ℝ => iteratedFDeriv ℝ (j + 1) (fun p => H (p, x.2)) x.1) =
        fun x => C (iteratedFDeriv ℝ j (fun p => D (p, x.2)) x.1) := by
      funext x
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq]
    exact C.contDiff.comp (ih (contDiff_parameter_fderiv hH))

theorem integrable_parameter_iteratedFDeriv_of_compact_time_support (j : ℕ)
    {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : P × ℝ → E} (hH : ContDiff ℝ ∞ H)
    {K : Set ℝ} (hK : IsCompact K) (hs : ∀ p t, t ∉ K → H (p, t) = 0) (p : P) :
    Integrable (fun t : ℝ => iteratedFDeriv ℝ j (fun p => H (p, t)) p) := by
  have hJ := (contDiff_parameter_iteratedFDeriv j hH).continuous.comp
    ((continuous_const (y := p)).prodMk continuous_id)
  apply hJ.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro hK
  intro t ht
  change iteratedFDeriv ℝ j (fun p => H (p, t)) p = 0
  have heq : (fun p => H (p, t)) = fun _ => (0 : E) := funext (fun p => hs p t ht)
  rw [heq]
  cases j with
  | zero => simp
  | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply]

set_option maxHeartbeats 800000 in
/-- All finite jets of the actual integral equal integrals of the actual
jets. The proof iterates the first derivative theorem in Banach spaces. -/
theorem iteratedFDeriv_integral_of_compact_time_support (j : ℕ)
    {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : P × ℝ → E} (hH : ContDiff ℝ ∞ H)
    {K : Set ℝ} (hK : IsCompact K) (hs : ∀ p t, t ∉ K → H (p, t) = 0) (p : P) :
    iteratedFDeriv ℝ j (fun p => ∫ t : ℝ, H (p, t)) p =
      ∫ t : ℝ, iteratedFDeriv ℝ j (fun p => H (p, t)) p := by
  induction j generalizing E with
  | zero =>
    exact ((continuousMultilinearCurryFin0 ℝ P E).symm.toContinuousLinearEquiv.integral_comp_comm
      (fun t => H (p, t))).symm
  | succ j ih =>
    let D : P × ℝ → P →L[ℝ] E := fun x => fderiv ℝ (fun p => H (p, x.2)) x.1
    let C := (continuousMultilinearCurryRightEquiv' ℝ j P E).symm.toContinuousLinearEquiv
    have hD : ContDiff ℝ ∞ D := contDiff_parameter_fderiv hH
    have hsD : ∀ p t, t ∉ K → D (p, t) = 0 := by
      intro p t ht
      have heq : (fun p => H (p, t)) = fun _ => (0 : E) := funext (fun p => hs p t ht)
      simp only [D, heq, fderiv_const_apply]
    have hderiv : fderiv ℝ (fun p => ∫ t : ℝ, H (p, t)) = fun p => ∫ t : ℝ, D (p, t) := by
      funext p
      exact (hasFDerivAt_integral_of_compact_time_support hH hK hs p).fderiv
    calc
      _ = C (iteratedFDeriv ℝ j (fun p => ∫ t : ℝ, D (p, t)) p) := by
        rw [iteratedFDeriv_succ_eq_comp_right, hderiv]
        rfl
      _ = C (∫ t : ℝ, iteratedFDeriv ℝ j (fun p => D (p, t)) p) := by rw [ih hD hsD]
      _ = ∫ t : ℝ, C (iteratedFDeriv ℝ j (fun p => D (p, t)) p) :=
        (C.toContinuousLinearMap.integral_comp_comm
          (integrable_parameter_iteratedFDeriv_of_compact_time_support j hD hK hsD p)).symm
      _ = ∫ t : ℝ, iteratedFDeriv ℝ (j + 1) (fun p => H (p, t)) p := by
        apply integral_congr_ae
        exact ae_of_all _ (fun t => (iteratedFDeriv_succ_eq_comp_right
          (𝕜 := ℝ) (n := j) (f := fun p => H (p, t)) (x := p)).symm)

theorem iteratedFDeriv_integral_apply_of_compact_time_support (j : ℕ)
    {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : P × ℝ → E} (hH : ContDiff ℝ ∞ H)
    {K : Set ℝ} (hK : IsCompact K) (hs : ∀ p t, t ∉ K → H (p, t) = 0)
    (p : P) (v : Fin j → P) :
    iteratedFDeriv ℝ j (fun p => ∫ t : ℝ, H (p, t)) p v =
      ∫ t : ℝ, iteratedFDeriv ℝ j (fun p => H (p, t)) p v := by
  rw [iteratedFDeriv_integral_of_compact_time_support j hH hK hs p]
  exact ContinuousMultilinearMap.integral_apply
    (integrable_parameter_iteratedFDeriv_of_compact_time_support j hH hK hs p) v

end PlanarNikodym
