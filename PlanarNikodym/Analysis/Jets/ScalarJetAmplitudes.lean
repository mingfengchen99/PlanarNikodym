import PlanarNikodym.Analysis.Jets.ScalarJetCoordinates
import PlanarNikodym.Analysis.Fourier.FourierReconstruction

/-! The two real compact amplitudes produced by an actual parameter
 derivative. These formulas retain the oscillatory average. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace PlanarNikodym

/-- A derivative of the real cutoff in a parameter direction. -/
def scalarJetCutoffDeriv {d : ℕ} (χ : Cutoff d) (v : Parameters 2 d) : Cutoff d :=
  fun x => fderiv ℝ χ x (0, v)

/-- The real amplitude from differentiating the curve height. -/
def Family.scalarJetPhaseCutoff {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (v : Parameters 2 d) : Cutoff d :=
  fun x => χ x * fderiv ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x (0, v)

theorem tsupport_scalarJetCutoffDeriv_subset {d : ℕ} (χ : Cutoff d)
    (v : Parameters 2 d) : tsupport (scalarJetCutoffDeriv χ v) ⊆ tsupport χ :=
  tsupport_fderiv_apply_subset ℝ (0, v)

theorem Family.tsupport_scalarJetPhaseCutoff_subset {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (v : Parameters 2 d) :
    tsupport (G.scalarJetPhaseCutoff χ v) ⊆ tsupport χ := tsupport_mul_subset_left

theorem contDiff_scalarJetCutoffDeriv {d : ℕ} (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (v : Parameters 2 d) :
    ContDiff ℝ ∞ (scalarJetCutoffDeriv χ v) := by
  exact (hχ.fderiv_right (by simp)).clm_apply contDiff_const

theorem Family.contDiff_scalarJetPhaseCutoff {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (v : Parameters 2 d) : ContDiff ℝ ∞ (G.scalarJetPhaseCutoff χ v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (((hγ x hx).fderiv_right (by simp)).clm_apply contDiffAt_const)
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [Family.scalarJetPhaseCutoff, hy]

theorem hasCompactSupport_scalarJetCutoffDeriv {d : ℕ} (χ : Cutoff d)
    (hc : HasCompactSupport χ) (v : Parameters 2 d) :
    HasCompactSupport (scalarJetCutoffDeriv χ v) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_scalarJetCutoffDeriv_subset χ v)

theorem Family.hasCompactSupport_scalarJetPhaseCutoff {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hc : HasCompactSupport χ) (v : Parameters 2 d) :
    HasCompactSupport (G.scalarJetPhaseCutoff χ v) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (G.tsupport_scalarJetPhaseCutoff_subset χ v)

/-- The vertical input derivative, before any norm is taken. -/
def scalarJetVertical (f : Plane → ℂ) : Plane → ℂ := fun x => fderiv ℝ f x (0, 1)

theorem contDiff_scalarJetVertical {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scalarJetVertical f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- Actual differentiation preserves a finite sum of oscillatory averages.
Both resulting amplitudes are smooth and supported in the original cutoff. -/
theorem Family.fderiv_cutoffAverage_scalarJet {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (q v : Parameters 2 d) :
    fderiv ℝ (G.cutoffAverage χ f) q v =
      G.cutoffAverage (scalarJetCutoffDeriv χ v) f q +
      G.cutoffAverage (G.scalarJetPhaseCutoff χ v) (scalarJetVertical f) q := by
  have hd := contDiff_scalarJetCutoffDeriv χ hχ v
  have hdc := hasCompactSupport_scalarJetCutoffDeriv χ hc v
  have hp := G.contDiff_scalarJetPhaseCutoff χ hχ hγ v
  have hpc := G.hasCompactSupport_scalarJetPhaseCutoff χ hc v
  have hgd := fun x hx => hγ x (tsupport_scalarJetCutoffDeriv_subset χ v hx)
  have hgp := fun x hx => hγ x (G.tsupport_scalarJetPhaseCutoff_subset χ v hx)
  rw [G.fderiv_cutoffAverage_apply χ hχ hc hγ hf q v]
  change (∫ t, _) = (∫ t, _) + ∫ t, _
  rw [← integral_add (G.cutoffIntegrand_integrable _ hd.continuous hdc (fun x hx => (hgd x hx).continuousAt) hf.continuous q)
    (G.cutoffIntegrand_integrable _ hp.continuous hpc (fun x hx => (hgp x hx).continuousAt)
      (contDiff_scalarJetVertical hf).continuous q)]
  apply integral_congr_ae
  filter_upwards [] with t
  have hχder : fderiv ℝ (fun r => χ (t, r)) q v =
      fderiv ℝ χ (t, q) (0, v) := by
    have h := (hχ.differentiable (by simp) (t, q)).hasFDerivAt.comp q
      ((hasFDerivAt_const t q).prodMk (hasFDerivAt_id q))
    exact congrArg (fun D : Parameters 2 d →L[ℝ] ℝ => D v) h.fderiv
  rw [hχder]
  congr 1
  by_cases hx : (t, q) ∈ tsupport χ
  · have hγder : fderiv ℝ (fun r => G.γ t r) q v =
        fderiv ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) (t, q) (0, v) := by
      have h := ((hγ (t, q) hx).differentiableAt (by simp)).hasFDerivAt.comp q
        ((hasFDerivAt_const t q).prodMk (hasFDerivAt_id q))
      exact congrArg (fun D : Parameters 2 d →L[ℝ] ℝ => D v) h.fderiv
    rw [hγder]
    dsimp [Family.scalarJetPhaseCutoff, scalarJetVertical]
    rw [show ((0, fderiv ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) (t, q) (0, v)) : Plane) =
      fderiv ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) (t, q) (0, v) • ((0, 1) : Plane) by
        simp, map_smul, Complex.ofReal_mul, Complex.real_smul]
    ring
  · simp [Family.scalarJetPhaseCutoff, image_eq_zero_of_notMem_tsupport hx]

end PlanarNikodym
