import PlanarNikodym.Analysis.Fourier.GlyzProjectiveCurve
import PlanarNikodym.Analysis.Fourier.GlyzConicGeometry

/-! Smooth projective charts constructed from a nonzero actual full-jet
determinant. A compactly supported interpolation replaces the local
denominator by a globally positive smooth function, so the resulting
base curve is globally smooth and fits the general curve theorem. -/
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace PlanarNikodym

theorem exists_glyz_positive_denominator_extension {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (a : E → ℝ) (ha : ContDiff ℝ ∞ a) (s : E) (hs : a s = 1) :
    ∃ b : E → ℝ, ContDiff ℝ ∞ b ∧ (∀ t, 1 / 2 < b t) ∧ b =ᶠ[𝓝 s] a := by
  have hn : {t | 1 / 2 < a t} ∈ 𝓝 s :=
    ha.continuous.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by rw [hs]; norm_num))
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hn
  let χ : ContDiffBump s := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  let b : E → ℝ := fun t => 1 + χ t * (a t - 1)
  refine ⟨b, contDiff_const.add (χ.contDiff.mul (ha.sub contDiff_const)), ?_, ?_⟩
  · intro t
    by_cases ht : χ t = 0
    · norm_num [b, ht]
    · have hχ : 0 < χ t := lt_of_le_of_ne χ.nonneg (Ne.symm ht)
      have htball : t ∈ ball s ρ := by
        change t ∈ ball s χ.rOut
        rw [← χ.support_eq]
        exact ht
      have hat : 1 / 2 < a t := hball htball
      have hm := mul_pos hχ (sub_pos.mpr hat)
      dsimp [b]
      nlinarith [χ.le_one (x := t)]
  · filter_upwards [χ.eventuallyEq_one] with t ht
    simp only [b, ht, Pi.one_apply, one_mul, add_sub_cancel]

theorem glyzCurveJetOperator_det_eq_matrix {k : ℕ} (γ : ℝ → GlyzSpace k) (s : ℝ) :
    (glyzCurveJetOperator γ s).det =
      Matrix.det (fun i j : Fin k => iteratedDeriv ((j : ℕ) + 1) γ s i) := by
  change LinearMap.det (glyzCurveJetOperator γ s).toLinearMap = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin k) ℝ).toBasis]
  congr 1
  ext i j
  simp only [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe]
  change (glyzCurveJetOperator γ s (EuclideanSpace.basisFun (Fin k) ℝ j)) i = _
  rw [glyzCurveJetOperator_basis]

 theorem continuous_glyzCurveJetOperator_det {k : ℕ} (γ : ℝ → GlyzSpace k)
    (hγ : ContDiff ℝ ∞ γ) : Continuous (fun s => (glyzCurveJetOperator γ s).det) := by
  simp_rw [glyzCurveJetOperator_det_eq_matrix]
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
    (hγ.continuous_iteratedDeriv ((j : ℕ) + 1)
      (by exact_mod_cast (le_top : (((j : ℕ) + 1 : ℕ) : ℕ∞) ≤ ⊤)))

/-- A smooth vector curve has uniform bounds for any prescribed finite
number of actual derivatives on a compact interval. -/
theorem exists_glyz_curve_derivative_bound_closedBall {k : ℕ} (γ : ℝ → GlyzSpace k)
    (hγ : ContDiff ℝ ∞ γ) (s ρ : ℝ) (M : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ closedBall s ρ, ∀ j ≤ M, ‖iteratedDeriv j γ t‖ ≤ B := by
  let H : ℝ → Fin (M + 1) → GlyzSpace k := fun t j => iteratedDeriv (j : ℕ) γ t
  have hH : Continuous H := continuous_pi fun j => hγ.continuous_iteratedDeriv j
    (by exact_mod_cast (le_top : ((j : ℕ) : ℕ∞) ≤ ⊤))
  obtain ⟨B, hB⟩ := (isCompact_closedBall s ρ).exists_bound_of_continuousOn hH.continuousOn
  refine ⟨|B| + 1, by positivity, fun t ht j hj => ?_⟩
  calc
    _ ≤ ‖H t‖ := norm_le_pi_norm (H t) (⟨j, by omega⟩ : Fin (M + 1))
    _ ≤ B := hB t ht
    _ ≤ |B| + 1 := by linarith [le_abs_self B]


/-- Fixed coordinate order: the radial coordinate is the first jet
coordinate, followed by the horizontal coordinates. -/
def glyzConeToJetLinearEquiv (k : ℕ) : GlyzConeSpace k ≃ₗ[ℝ] GlyzSpace (k + 1) where
  toFun z := WithLp.toLp 2 (Fin.cons (WithLp.ofLp z).2 (WithLp.ofLp (WithLp.ofLp z).1))
  invFun z := WithLp.toLp 2 (glyzProjectiveHorizontal k z, z 0)
  left_inv z := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · ext i; rfl
    · rfl
  right_inv z := by ext i; cases i using Fin.cases <;> rfl
  map_add' z w := by ext i; cases i using Fin.cases <;> rfl
  map_smul' c z := by ext i; cases i using Fin.cases <;> rfl

def glyzConeToJetEquiv (k : ℕ) : GlyzConeSpace k ≃L[ℝ] GlyzSpace (k + 1) :=
  (glyzConeToJetLinearEquiv k).toContinuousLinearEquiv

/-- An actual nonzero full-jet determinant produces a projective chart,
a globally smooth base curve, a globally positive smooth radial factor,
and quantitative derivative and torsion bounds on one genuine interval. -/
theorem exists_glyz_projective_curve_chart (k M : ℕ) (Γ : ℝ → GlyzSpace (k + 1))
    (hΓ : ContDiff ℝ ∞ Γ) (s : ℝ) (hdet : (glyzCurveFullJetOperator k Γ s).det ≠ 0) :
    ∃ (A : GlyzConeSpace k ≃L[ℝ] GlyzSpace (k + 1)) (a : ℝ → ℝ)
      (γ : ℝ → GlyzSpace k) (ρ B : ℝ),
      ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ γ ∧ 0 < ρ ∧ 0 < B ∧
      (∀ t, 1 / 2 < a t) ∧
      (∀ t ∈ closedBall s ρ, Γ t = A (WithLp.toLp 2 (a t • γ t, a t))) ∧
      (∀ t ∈ closedBall s ρ, 1 / 2 ≤ |(glyzCurveJetOperator γ t).det|) ∧
      (∀ t ∈ closedBall s ρ, ∀ j ≤ M, ‖iteratedDeriv j γ t‖ ≤ B) := by
  let L := (glyzCurveFullJetOperator k Γ s).toContinuousLinearEquivOfDetNeZero hdet
  have hL : L.toContinuousLinearMap = glyzCurveFullJetOperator k Γ s :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  let F : ℝ → GlyzSpace (k + 1) := fun t => L.symm (Γ t)
  have hF : ContDiff ℝ ∞ F := L.symm.contDiff.comp hΓ
  have hFjet := glyz_normalized_full_jet k Γ s L hL
  let b : ℝ → ℝ := fun t => F t 0
  have hb : ContDiff ℝ ∞ b :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (k + 1))).contDiff.comp hF
  have hb0 : b s = 1 := by
    have h := congrArg (fun x : GlyzSpace (k + 1) => x 0) (hFjet 0)
    simpa [b, F] using h
  obtain ⟨a, ha, hapos, hab⟩ := exists_glyz_positive_denominator_extension b hb s hb0
  let γ : ℝ → GlyzSpace k := fun t => (a t)⁻¹ • glyzProjectiveHorizontal k (F t)
  have ha0 (t : ℝ) : a t ≠ 0 := ne_of_gt (lt_trans (by norm_num) (hapos t))
  have hγ : ContDiff ℝ ∞ γ := (ha.inv ha0).smul ((glyzProjectiveHorizontal k).contDiff.comp hF)
  have hnear : γ =ᶠ[𝓝 s] glyzProjectiveCurve k F := by
    filter_upwards [hab] with t ht
    simp only [γ, glyzProjectiveCurve, ht, b]
  have hjet : glyzCurveJetOperator γ s = ContinuousLinearMap.id ℝ (GlyzSpace k) := by
    have he : glyzCurveJetOperator γ s = glyzCurveJetOperator (glyzProjectiveCurve k F) s := by
      unfold glyzCurveJetOperator
      congr 1
      funext j
      exact (hnear.iteratedDeriv ((j : ℕ) + 1)).self_of_nhds
    rw [he]
    exact glyzProjectiveCurve_jet_eq_id k F s hF hFjet
  have hdetnear : ∀ᶠ t in 𝓝 s, 1 / 2 < (glyzCurveJetOperator γ t).det :=
    (continuous_glyzCurveJetOperator_det γ hγ).continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (by rw [hjet]; change (1 / 2 : ℝ) < LinearMap.det (LinearMap.id : GlyzSpace k →ₗ[ℝ] GlyzSpace k); norm_num))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (hab.and hdetnear)
  have hclosed : closedBall s (ρ / 2) ⊆ ball s ρ := closedBall_subset_ball (by linarith)
  obtain ⟨B, hB, hder⟩ := exists_glyz_curve_derivative_bound_closedBall γ hγ s (ρ / 2) M
  let A := (glyzConeToJetEquiv k).trans L
  refine ⟨A, a, γ, ρ / 2, B, ha, hγ, by positivity, hB, hapos, ?_, ?_, hder⟩
  · intro t ht
    have hat : a t = b t := (hρsub (hclosed ht)).1
    apply L.symm.injective
    change F t = L.symm (L (glyzConeToJetEquiv k (WithLp.toLp 2 (a t • γ t, a t))))
    rw [ContinuousLinearEquiv.symm_apply_apply]
    ext i
    cases i using Fin.cases with
    | zero => exact hat.symm
    | succ i =>
      change F t i.succ = a t * ((a t)⁻¹ * F t i.succ)
      rw [← mul_assoc, mul_inv_cancel₀ (ha0 t), one_mul]
  · intro t ht
    exact (hρsub (hclosed ht)).2.le.trans (le_abs_self _)

end PlanarNikodym
