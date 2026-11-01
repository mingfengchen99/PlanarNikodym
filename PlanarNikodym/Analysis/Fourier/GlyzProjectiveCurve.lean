import PlanarNikodym.Analysis.Fourier.GlyzGeneralCurveLocalization
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Actual projective normalization of a nondegenerate conic curve.
The full jet provides fixed linear coordinates in which the denominator
has constant jet and the horizontal derivatives form the standard basis. -/
noncomputable section
open Set Filter
open scoped BigOperators ContDiff Topology
namespace PlanarNikodym

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem glyz_iteratedDeriv_comp_clm (L : E →L[ℝ] F) (f : ℝ → E) (s : ℝ)
    (n : ℕ) (hf : ContDiffAt ℝ n f s) :
    iteratedDeriv n (fun t => L (f t)) s = L (iteratedDeriv n f s) := by
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ n (L ∘ f) s (fun _ => 1) = _
  rw [L.iteratedFDeriv_comp_left hf le_rfl]
  rfl

theorem glyz_iteratedDeriv_comp_cle (L : E ≃L[ℝ] F) (f : ℝ → E) (s : ℝ) (n : ℕ) :
    iteratedDeriv n (fun t => L (f t)) s = L (iteratedDeriv n f s) := by
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ n (L ∘ f) s (fun _ => 1) = _
  rw [L.iteratedFDeriv_comp_left]
  rfl

theorem glyz_iteratedDeriv_smul (a : ℝ → ℝ) (f : ℝ → E) (s : ℝ) (n : ℕ)
    (ha : ContDiffAt ℝ n a s) (hf : ContDiffAt ℝ n f s) :
    iteratedDeriv n (fun t => a t • f t) s =
      ∑ j ∈ Finset.range (n + 1), n.choose j • iteratedDeriv j a s • iteratedDeriv (n - j) f s := by
  simpa only [iteratedDerivWithin_univ, Pi.smul_def'] using
    iteratedDerivWithin_smul (mem_univ s) uniqueDiffOn_univ ha.contDiffWithinAt hf.contDiffWithinAt

/-- Division by a scalar whose jet is constant preserves every jet of
the numerator, after normalization of its value to one. -/
theorem glyz_iteratedDeriv_projective_normalized (a : ℝ → ℝ) (X : ℝ → E)
    (s : ℝ) (n : ℕ) (ha : ContDiffAt ℝ n a s) (hX : ContDiffAt ℝ n X s)
    (ha0 : a s = 1) (hflat : ∀ j, 0 < j → j ≤ n → iteratedDeriv j a s = 0) :
    iteratedDeriv n (fun t => (a t)⁻¹ • X t) s = iteratedDeriv n X s := by
  let γ := fun t => (a t)⁻¹ • X t
  have ha_ne : a s ≠ 0 := by rw [ha0]; norm_num
  have hγ : ContDiffAt ℝ n γ s := (ha.inv ha_ne).smul hX
  have hnear : X =ᶠ[𝓝 s] fun t => a t • γ t := by
    filter_upwards [ha.continuousAt.eventually_ne ha_ne] with t ht
    simp [γ, smul_smul, ht]
  have h := (hnear.iteratedDeriv n).self_of_nhds
  rw [glyz_iteratedDeriv_smul a γ s n ha hγ] at h
  have hsum : (∑ j ∈ Finset.range (n + 1),
      n.choose j • iteratedDeriv j a s • iteratedDeriv (n - j) γ s) = iteratedDeriv n γ s := by
    rw [Finset.sum_eq_single 0]
    · simp [ha0]
    · intro j hj hj0
      rw [hflat j (by omega) (by have hj' := Finset.mem_range.mp hj; omega)]
      simp
    · simp
  rw [hsum] at h
  exact h.symm

def glyzCurveFullJetOperator (k : ℕ) (Γ : ℝ → GlyzSpace (k + 1)) (s : ℝ) :
    GlyzSpace (k + 1) →L[ℝ] GlyzSpace (k + 1) :=
  (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis.constrL
    (fun j : Fin (k + 1) => iteratedDeriv (j : ℕ) Γ s)

theorem glyzCurveFullJetOperator_basis (k : ℕ) (Γ : ℝ → GlyzSpace (k + 1)) (s : ℝ)
    (j : Fin (k + 1)) :
    glyzCurveFullJetOperator k Γ s (EuclideanSpace.basisFun (Fin (k + 1)) ℝ j) =
      iteratedDeriv (j : ℕ) Γ s := Module.Basis.constrL_basis _ _ _

def glyzProjectiveHorizontal (k : ℕ) : GlyzSpace (k + 1) →L[ℝ] GlyzSpace k :=
  ({ toFun := fun x => WithLp.toLp 2 (fun j : Fin k => x j.succ)
     map_add' := by intro x y; rfl
     map_smul' := by intro c x; rfl } : GlyzSpace (k + 1) →ₗ[ℝ] GlyzSpace k).toContinuousLinearMap

@[simp] theorem glyzProjectiveHorizontal_apply (k : ℕ) (x : GlyzSpace (k + 1)) (j : Fin k) :
    glyzProjectiveHorizontal k x j = x j.succ := rfl

def glyzProjectiveCurve (k : ℕ) (Γ : ℝ → GlyzSpace (k + 1)) (s : ℝ) : GlyzSpace k :=
  (Γ s 0)⁻¹ • glyzProjectiveHorizontal k (Γ s)

/-- The actual fixed inverse jet normalizes the whole conic jet. -/
theorem glyz_normalized_full_jet (k : ℕ) (Γ : ℝ → GlyzSpace (k + 1)) (s : ℝ)
    (L : GlyzSpace (k + 1) ≃L[ℝ] GlyzSpace (k + 1))
    (hL : L.toContinuousLinearMap = glyzCurveFullJetOperator k Γ s) (j : Fin (k + 1)) :
    iteratedDeriv (j : ℕ) (fun t => L.symm (Γ t)) s = EuclideanSpace.basisFun (Fin (k + 1)) ℝ j := by
  rw [glyz_iteratedDeriv_comp_cle]
  have h := glyzCurveFullJetOperator_basis k Γ s j
  rw [← hL] at h
  rw [← h]
  exact L.symm_apply_apply _

/-- In normalized full-jet coordinates, the projective curve has the
identity derivative frame at the base point. -/
theorem glyzProjectiveCurve_jet_eq_id (k : ℕ) (Γ : ℝ → GlyzSpace (k + 1)) (s : ℝ)
    (hΓ : ContDiff ℝ ∞ Γ)
    (hjet : ∀ j : Fin (k + 1), iteratedDeriv (j : ℕ) Γ s = EuclideanSpace.basisFun (Fin (k + 1)) ℝ j) :
    glyzCurveJetOperator (glyzProjectiveCurve k Γ) s = ContinuousLinearMap.id ℝ (GlyzSpace k) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.ext
  intro j
  change glyzCurveJetOperator (glyzProjectiveCurve k Γ) s
    (EuclideanSpace.basisFun (Fin k) ℝ j) = EuclideanSpace.basisFun (Fin k) ℝ j
  rw [glyzCurveJetOperator_basis]
  have ha : ContDiff ℝ ∞ (fun t => Γ t 0) := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (k + 1))).contDiff.comp hΓ
  have hX : ContDiff ℝ ∞ (fun t => glyzProjectiveHorizontal k (Γ t)) :=
    (glyzProjectiveHorizontal k).contDiff.comp hΓ
  have ha0 : Γ s 0 = 1 := by
    have h := congrArg (fun x : GlyzSpace (k + 1) => x 0) (hjet 0)
    simpa using h
  have hflat : ∀ i, 0 < i → i ≤ (j : ℕ) + 1 → iteratedDeriv i (fun t => Γ t 0) s = 0 := by
    intro i hi hij
    have hi' : i < k + 1 := by omega
    change iteratedDeriv i (fun t => (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (k + 1))) (Γ t)) s = 0
    rw [glyz_iteratedDeriv_comp_clm (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (k + 1))) Γ s i (hΓ.of_le (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))).contDiffAt,
      hjet ⟨i, hi'⟩]
    simp [EuclideanSpace.basisFun_apply, Fin.ext_iff, hi.ne']
  rw [show glyzProjectiveCurve k Γ = (fun t => (Γ t 0)⁻¹ • glyzProjectiveHorizontal k (Γ t)) from rfl,
    glyz_iteratedDeriv_projective_normalized _ _ s ((j : ℕ) + 1)
      (ha.of_le (by exact_mod_cast (le_top : (((j : ℕ) + 1 : ℕ) : ℕ∞) ≤ ⊤))).contDiffAt (hX.of_le (by exact_mod_cast (le_top : (((j : ℕ) + 1 : ℕ) : ℕ∞) ≤ ⊤))).contDiffAt ha0 hflat,
    glyz_iteratedDeriv_comp_clm (glyzProjectiveHorizontal k) Γ s ((j : ℕ) + 1)
      (hΓ.of_le (by exact_mod_cast (le_top : (((j : ℕ) + 1 : ℕ) : ℕ∞) ≤ ⊤))).contDiffAt]
  have hjjet : iteratedDeriv ((j : ℕ) + 1) Γ s = EuclideanSpace.basisFun (Fin (k + 1)) ℝ j.succ := by
    simpa only [Fin.val_succ] using hjet j.succ
  rw [hjjet]
  ext i
  simp [EuclideanSpace.basisFun_apply]

end PlanarNikodym
