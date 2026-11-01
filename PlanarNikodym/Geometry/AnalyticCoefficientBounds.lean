import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Data.Fintype.Powerset

/-! Uniform coefficient bounds for lifting joint analytic germs to the
Banach space of bounded sequences. -/
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A uniformly bounded family of multilinear maps defines an actual
continuous multilinear map into the Banach space of bounded sequences. -/
def boundedSequenceMultilinear {k : ℕ} (L : ℕ → E [×k]→L[ℝ] ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hL : ∀ n, ‖L n‖ ≤ C) :
    E [×k]→L[ℝ] (lp (fun _ : ℕ => ℝ) ∞) :=
  MultilinearMap.mkContinuous
    { toFun := fun v => ⟨fun n => L n v, memℓp_infty
        ⟨C * ∏ i, ‖v i‖, by
          rintro _ ⟨n, rfl⟩
          exact (L n).le_of_opNorm_le (hL n) v⟩⟩
      map_update_add' := by
        intro _ v i x y
        apply lp.ext
        funext n
        exact (L n).map_update_add v i x y
      map_update_smul' := by
        intro _ v i c x
        apply lp.ext
        funext n
        exact (L n).map_update_smul v i c x }
    C (fun v => lp.norm_le_of_forall_le (by positivity)
      (fun n => (L n).le_of_opNorm_le (hL n) v))

@[simp] theorem boundedSequenceMultilinear_apply {k : ℕ}
    (L : ℕ → E [×k]→L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C) (hL : ∀ n, ‖L n‖ ≤ C)
    (v : Fin k → E) (n : ℕ) : boundedSequenceMultilinear L C hC hL v n = L n v := rfl

theorem norm_boundedSequenceMultilinear_le {k : ℕ}
    (L : ℕ → E [×k]→L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C) (hL : ∀ n, ‖L n‖ ≤ C) :
    ‖boundedSequenceMultilinear L C hC hL‖ ≤ C :=
  MultilinearMap.mkContinuous_norm_le _ hC _

/-- A coarse combinatorial bound sufficient for a common convergence radius. -/
theorem norm_changeOriginSeries_le_two_pow
    (p : FormalMultilinearSeries ℝ E ℝ) (n k : ℕ) :
    ‖p.changeOriginSeries n k‖ ≤ (2 : ℝ) ^ (n + k) * ‖p (n + k)‖ := by
  have hb : ‖p.changeOriginSeries n k‖ ≤
      (Fintype.card {s : Finset (Fin (n + k)) // s.card = k} : ℝ) * ‖p (n + k)‖ := by
    have ht := p.nnnorm_changeOriginSeries_le_tsum n k
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ht
    exact_mod_cast ht
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hc := Fintype.card_le_of_injective
    (fun s : {s : Finset (Fin (n + k)) // s.card = k} => s.val) Subtype.val_injective
  simpa using (show (Fintype.card {s : Finset (Fin (n + k)) // s.card = k} : ℝ) ≤
    Fintype.card (Finset (Fin (n + k))) by exact_mod_cast hc)

/-- The parameter-homogeneous term of one rescaled vertical coefficient. -/
def analyticCoefficientTerm (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ)
    (s : ℝ) (k n : ℕ) : E [×k]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E × ℝ) ℝ
    (fun _ => (0, s))).compContinuousMultilinearMap
      ((p.changeOriginSeries n k).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ E ℝ))

@[simp] theorem analyticCoefficientTerm_apply
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ) (s : ℝ) (k n : ℕ) (v : Fin k → E) :
    analyticCoefficientTerm p s k n v =
      p.changeOriginSeries n k (fun i => (v i, 0)) (fun _ => (0, s)) := rfl

theorem norm_analyticCoefficientTerm_le
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ) {s : ℝ} (hs : 0 ≤ s) (k n : ℕ) :
    ‖analyticCoefficientTerm p s k n‖ ≤
      (2 : ℝ) ^ (n + k) * ‖p (n + k)‖ * s ^ n := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  calc
    ‖analyticCoefficientTerm p s k n v‖ ≤
        ‖p.changeOriginSeries n k (fun i => (v i, 0))‖ * s ^ n := by
      simpa [analyticCoefficientTerm_apply, Prod.norm_def, Real.norm_eq_abs,
        abs_of_nonneg hs, max_eq_right hs] using
        (p.changeOriginSeries n k (fun i => (v i, 0))).le_opNorm (fun _ => (0, s))
    _ ≤ (‖p.changeOriginSeries n k‖ * ∏ i, ‖v i‖) * s ^ n := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa [Prod.norm_def] using (p.changeOriginSeries n k).le_opNorm (fun i => (v i, 0))
    _ ≤ ((2 : ℝ) ^ (n + k) * ‖p (n + k)‖ * ∏ i, ‖v i‖) * s ^ n := by
      gcongr
      exact norm_changeOriginSeries_le_two_pow p n k
    _ = _ := by ring

end PlanarNikodym
