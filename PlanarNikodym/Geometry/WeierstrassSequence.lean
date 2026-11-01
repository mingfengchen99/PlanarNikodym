import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Analytic.Constructions

/-! The Banach space of bounded coefficients and its exact head/tail decomposition.
Bounded real coefficients define convergent power series for `|t| < 1`. -/

noncomputable section
open scoped ENNReal Topology
open Set

namespace PlanarNikodym

abbrev WeierstrassSeries := lp (fun _ : ℕ => ℝ) ∞

/-- Remove the first `m` coefficients. -/
def weierstrassTail (m : ℕ) : WeierstrassSeries →L[ℝ] WeierstrassSeries :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun n => u (n + m),
        memℓp_infty ⟨‖u‖, by
          rintro _ ⟨n, rfl⟩
          exact lp.norm_apply_le_norm ENNReal.top_ne_zero u _⟩⟩
      map_add' := fun u v => by ext n; rfl
      map_smul' := fun c u => by ext n; rfl }
    1 (fun u => by
      simp only [one_mul]
      exact lp.norm_le_of_forall_le (norm_nonneg u)
        (fun n => lp.norm_apply_le_norm ENNReal.top_ne_zero u _))

@[simp]
theorem weierstrassTail_apply (m : ℕ) (u : WeierstrassSeries) (n : ℕ) :
    weierstrassTail m u n = u (n + m) := rfl

/-- The first `m` coefficients. -/
def weierstrassHead (m : ℕ) : WeierstrassSeries →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi fun i => lp.evalCLM ℝ (fun _ : ℕ => ℝ) ∞ (i : ℕ)

@[simp]
theorem weierstrassHead_apply (m : ℕ) (u : WeierstrassSeries) (i : Fin m) :
    weierstrassHead m u i = u i := rfl

/-- Glue a finite head and an infinite bounded tail. -/
def weierstrassGlue (m : ℕ) : ((Fin m → ℝ) × WeierstrassSeries) →L[ℝ] WeierstrassSeries :=
  LinearMap.mkContinuous
    { toFun := fun z =>
        ⟨fun n => if hn : n < m then z.1 ⟨n, hn⟩ else z.2 (n - m),
          memℓp_infty ⟨‖z‖, by
            rintro _ ⟨n, rfl⟩
            dsimp only
            split_ifs with hn
            · exact (norm_le_pi_norm z.1 ⟨n, hn⟩).trans (norm_fst_le z)
            · exact (lp.norm_apply_le_norm ENNReal.top_ne_zero z.2 _).trans (norm_snd_le z)⟩⟩
      map_add' := fun z w => by
        ext n
        dsimp
        split_ifs <;> rfl
      map_smul' := fun c z => by
        ext n
        dsimp
        split_ifs <;> rfl }
    1 (fun z => by
      simp only [one_mul]
      apply lp.norm_le_of_forall_le (norm_nonneg z)
      intro n
      dsimp
      split_ifs with hn
      · exact (norm_le_pi_norm z.1 ⟨n, hn⟩).trans (norm_fst_le z)
      · exact (lp.norm_apply_le_norm ENNReal.top_ne_zero z.2 _).trans (norm_snd_le z))

@[simp]
theorem weierstrassGlue_apply_lt (m : ℕ) (a : Fin m → ℝ) (u : WeierstrassSeries)
    {n : ℕ} (hn : n < m) :
    weierstrassGlue m (a, u) n = a ⟨n, hn⟩ := by
  exact dif_pos hn

@[simp]
theorem weierstrassGlue_apply_add (m : ℕ) (a : Fin m → ℝ)
    (u : WeierstrassSeries) (n : ℕ) :
    weierstrassGlue m (a, u) (n + m) = u n := by
  change (if h : n + m < m then a ⟨n + m, h⟩ else u (n + m - m)) = u n
  simp

/-- Exact continuous linear splitting into the polynomial remainder and the quotient by `X^m`. -/
def weierstrassSplit (m : ℕ) :
    WeierstrassSeries ≃L[ℝ] ((Fin m → ℝ) × WeierstrassSeries) :=
  ContinuousLinearEquiv.equivOfInverse
    ((weierstrassHead m).prod (weierstrassTail m)) (weierstrassGlue m)
    (fun u => by
      ext n
      change (if hn : n < m then u n else u (n - m + m)) = u n
      split_ifs with hn
      · rfl
      · rw [Nat.sub_add_cancel (Nat.le_of_not_gt hn)])
    (fun z => by
      apply Prod.ext
      · funext i
        exact weierstrassGlue_apply_lt m z.1 z.2 i.2
      · ext n
        exact weierstrassGlue_apply_add m z.1 z.2 n)

@[simp]
theorem weierstrassSplit_apply (m : ℕ) (u : WeierstrassSeries) :
    weierstrassSplit m u = (weierstrassHead m u, weierstrassTail m u) := rfl

@[simp]
theorem weierstrassSplit_symm_apply (m : ℕ) (z : (Fin m → ℝ) × WeierstrassSeries) :
    (weierstrassSplit m).symm z = weierstrassGlue m z := rfl

/-- Multiplication by `X^m` on bounded coefficients. -/
def weierstrassShift (m : ℕ) : WeierstrassSeries →L[ℝ] WeierstrassSeries :=
  (weierstrassGlue m).comp (ContinuousLinearMap.inr ℝ (Fin m → ℝ) WeierstrassSeries)

theorem weierstrassShift_apply (m : ℕ) (u : WeierstrassSeries) (n : ℕ) :
    weierstrassShift m u n = if m ≤ n then u (n - m) else 0 := by
  change (if hn : n < m then (0 : Fin m → ℝ) ⟨n, hn⟩ else u (n - m)) = _
  by_cases hn : n < m <;> simp [hn, Nat.not_le_of_gt, Nat.le_of_not_gt]

@[simp]
theorem weierstrassShift_apply_add (m : ℕ) (u : WeierstrassSeries) (n : ℕ) :
    weierstrassShift m u (n + m) = u n := by
  simp [weierstrassShift_apply]

@[simp]
theorem weierstrassShift_apply_lt {m n : ℕ} (u : WeierstrassSeries) (hn : n < m) :
    weierstrassShift m u n = 0 := by
  simp [weierstrassShift_apply, Nat.not_le_of_gt hn]

@[simp]
theorem weierstrassShift_single_zero (m : ℕ) :
    weierstrassShift m (lp.single ∞ 0 (1 : ℝ)) = lp.single ∞ m (1 : ℝ) := by
  ext n
  rw [weierstrassShift_apply]
  by_cases hm : m ≤ n
  · simp only [if_pos hm, lp.single_apply, Pi.single_apply]
    by_cases he : n = m
    · subst n
      simp
    · simp [he, Nat.sub_ne_zero_of_lt (lt_of_le_of_ne hm (Ne.symm he))]
  · simp only [if_neg hm, lp.single_apply, Pi.single_apply]
    simp [show n ≠ m by omega]

theorem weierstrassGlue_eq (m : ℕ) (a : Fin m → ℝ) (u : WeierstrassSeries) :
    weierstrassGlue m (a, u) =
      (∑ i : Fin m, a i • lp.single ∞ (i : ℕ) (1 : ℝ)) + weierstrassShift m u := by
  ext n
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
  by_cases hn : n < m
  · rw [weierstrassGlue_apply_lt _ _ _ hn, weierstrassShift_apply_lt u hn, add_zero]
    symm
    rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin m)]
    · simp
    · intro b _ hbn
      simp [Pi.single_eq_of_ne (show n ≠ b.val by
        intro h
        apply hbn
        exact Fin.ext h.symm)]
    · simp
  · have hm : m ≤ n := Nat.le_of_not_gt hn
    change (if h : n < m then a ⟨n, h⟩ else u (n - m)) = _
    rw [dif_neg hn, weierstrassShift_apply, if_pos hm]
    have hs : ∑ i : Fin m, a i * (Pi.single (i : ℕ) (1 : ℝ) : ℕ → ℝ) n = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [Pi.single_eq_of_ne (show n ≠ i.val by omega)]
    rw [hs, zero_add]

end PlanarNikodym
