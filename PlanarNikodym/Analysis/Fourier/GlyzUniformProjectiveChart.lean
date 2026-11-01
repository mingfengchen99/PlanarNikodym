import PlanarNikodym.Analysis.Fourier.GlyzProjectiveChart
import PlanarNikodym.Analysis.Jets.CutoffGraphJetBounds

/-! A fixed projective coordinate chart for a whole jointly smooth parameter
patch. Its torsion and all prescribed fiber derivatives are controlled
uniformly by compactness, from one actual nonzero full-jet determinant. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PlanarNikodym

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem continuous_glyz_fiber_iteratedDeriv {k : ℕ} (Γ : P × ℝ → GlyzSpace k)
    (hΓ : ContDiff ℝ ∞ Γ) (j : ℕ) :
    Continuous (fun z : P × ℝ => iteratedDeriv j (fun t => Γ (z.1, t)) z.2) := by
  have hs : ContDiff ℝ ∞ (fun z : ℝ × P => Γ (z.2, z.1)) := hΓ.comp (by fun_prop)
  have hc : Continuous (fun z : ℝ × P =>
      iteratedFDeriv ℝ j (fun t => Γ (z.2, t)) z.1) :=
    continuous_iff_continuousAt.mpr fun _ =>
      (contDiffAt_fiber_iteratedFDeriv j hs.contDiffAt).continuousAt
  have hswap := hc.comp (continuous_snd.prodMk continuous_fst :
    Continuous (fun z : P × ℝ => (z.2, z.1)))
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  exact hswap.eval continuous_const

theorem continuous_glyz_fiber_jet_det {k : ℕ} (γ : P × ℝ → GlyzSpace k)
    (hγ : ContDiff ℝ ∞ γ) :
    Continuous (fun z : P × ℝ => (glyzCurveJetOperator (fun t => γ (z.1, t)) z.2).det) := by
  simp_rw [glyzCurveJetOperator_det_eq_matrix]
  apply Continuous.matrix_det
  exact continuous_pi fun i => continuous_pi fun j =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
      (continuous_glyz_fiber_iteratedDeriv γ hγ ((j : ℕ) + 1))

/-- All constants and the ambient linear coordinate map precede every
parameter in the patch. The hypotheses concern only the original smooth
curve and its actual full-jet determinant at the patch center. -/
theorem exists_uniform_glyz_projective_chart [FiniteDimensional ℝ P]
    (k M : ℕ) (Γ : P × ℝ → GlyzSpace (k + 1)) (hΓ : ContDiff ℝ ∞ Γ)
    (w : P) (s : ℝ)
    (hdet : (glyzCurveFullJetOperator k (fun t => Γ (w, t)) s).det ≠ 0) :
    ∃ (A : GlyzConeSpace k ≃L[ℝ] GlyzSpace (k + 1)) (a : P × ℝ → ℝ)
      (γ : P × ℝ → GlyzSpace k) (ρ B : ℝ),
      ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ γ ∧ 0 < ρ ∧ 0 < B ∧
      (∀ z, 1 / 2 < a z) ∧
      (∀ z ∈ closedBall (w, s) ρ, a z ≤ B) ∧
      (∀ z ∈ closedBall (w, s) ρ, Γ z = A (WithLp.toLp 2 (a z • γ z, a z))) ∧
      (∀ z ∈ closedBall (w, s) ρ,
        1 / 2 ≤ |(glyzCurveJetOperator (fun t => γ (z.1, t)) z.2).det|) ∧
      (∀ z ∈ closedBall (w, s) ρ, ∀ j ≤ M,
        ‖iteratedDeriv j (fun t => γ (z.1, t)) z.2‖ ≤ B) := by
  let L := (glyzCurveFullJetOperator k (fun t => Γ (w, t)) s).toContinuousLinearEquivOfDetNeZero hdet
  have hL : L.toContinuousLinearMap = glyzCurveFullJetOperator k (fun t => Γ (w, t)) s :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  let F : P × ℝ → GlyzSpace (k + 1) := fun z => L.symm (Γ z)
  have hF : ContDiff ℝ ∞ F := L.symm.contDiff.comp hΓ
  have hFs : ContDiff ℝ ∞ (fun t => F (w, t)) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hFjet := glyz_normalized_full_jet k (fun t => Γ (w, t)) s L hL
  let b : P × ℝ → ℝ := fun z => F z 0
  have hb : ContDiff ℝ ∞ b :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (k + 1))).contDiff.comp hF
  have hb0 : b (w, s) = 1 := by
    have h := congrArg (fun x : GlyzSpace (k + 1) => x 0) (hFjet 0)
    simpa [b, F] using h
  obtain ⟨a, ha, hapos, hab⟩ := exists_glyz_positive_denominator_extension b hb (w, s) hb0
  let γ : P × ℝ → GlyzSpace k := fun z => (a z)⁻¹ • glyzProjectiveHorizontal k (F z)
  have ha0 (z : P × ℝ) : a z ≠ 0 := ne_of_gt (lt_trans (by norm_num) (hapos z))
  have hγ : ContDiff ℝ ∞ γ := (ha.inv ha0).smul ((glyzProjectiveHorizontal k).contDiff.comp hF)
  have hnear : (fun t => γ (w, t)) =ᶠ[𝓝 s] glyzProjectiveCurve k (fun t => F (w, t)) := by
    have habs := hab.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
    filter_upwards [habs] with t ht
    change a (w, t) = b (w, t) at ht
    simp only [γ, glyzProjectiveCurve, ht, b]
  have hjet : glyzCurveJetOperator (fun t => γ (w, t)) s = ContinuousLinearMap.id ℝ (GlyzSpace k) := by
    have he : glyzCurveJetOperator (fun t => γ (w, t)) s =
        glyzCurveJetOperator (glyzProjectiveCurve k (fun t => F (w, t))) s := by
      unfold glyzCurveJetOperator
      congr 1
      funext j
      exact (hnear.iteratedDeriv ((j : ℕ) + 1)).self_of_nhds
    rw [he]
    exact glyzProjectiveCurve_jet_eq_id k (fun t => F (w, t)) s hFs hFjet
  have hdetnear : ∀ᶠ z in 𝓝 (w, s),
      1 / 2 < (glyzCurveJetOperator (fun t => γ (z.1, t)) z.2).det :=
    (continuous_glyz_fiber_jet_det γ hγ).continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (by
        rw [hjet]
        change (1 / 2 : ℝ) < LinearMap.det (LinearMap.id : GlyzSpace k →ₗ[ℝ] GlyzSpace k)
        norm_num))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (hab.and hdetnear)
  have hclosed : closedBall (w, s) (ρ / 2) ⊆ ball (w, s) ρ := closedBall_subset_ball (by linarith)
  let H : P × ℝ → Fin (M + 1) → GlyzSpace k :=
    fun z j => iteratedDeriv (j : ℕ) (fun t => γ (z.1, t)) z.2
  have hH : Continuous H := continuous_pi fun j => continuous_glyz_fiber_iteratedDeriv γ hγ j
  obtain ⟨C, hC⟩ := (isCompact_closedBall (w, s) (ρ / 2)).exists_bound_of_continuousOn hH.continuousOn
  obtain ⟨D, hD⟩ := (isCompact_closedBall (w, s) (ρ / 2)).exists_bound_of_continuousOn ha.continuous.continuousOn
  let A := (glyzConeToJetEquiv k).trans L
  refine ⟨A, a, γ, ρ / 2, |C| + |D| + 1, ha, hγ, by positivity, by positivity, hapos, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hd := hD z hz
    simp only [Real.norm_eq_abs] at hd
    linarith [le_abs_self (a z), le_abs_self D, abs_nonneg C]
  · intro z hz
    have haz : a z = b z := (hρsub (hclosed hz)).1
    apply L.symm.injective
    change F z = L.symm (L (glyzConeToJetEquiv k (WithLp.toLp 2 (a z • γ z, a z))))
    rw [ContinuousLinearEquiv.symm_apply_apply]
    ext i
    cases i using Fin.cases with
    | zero => exact haz.symm
    | succ i =>
      change F z i.succ = a z * ((a z)⁻¹ * F z i.succ)
      rw [← mul_assoc, mul_inv_cancel₀ (ha0 z), one_mul]
  · intro z hz
    exact (hρsub (hclosed hz)).2.le.trans (le_abs_self _)
  · intro z hz j hj
    have hc := (norm_le_pi_norm (H z) (⟨j, by omega⟩ : Fin (M + 1))).trans (hC z hz)
    change ‖iteratedDeriv j (fun t => γ (z.1, t)) z.2‖ ≤ _ at hc
    linarith [le_abs_self C, abs_nonneg D]

end PlanarNikodym
