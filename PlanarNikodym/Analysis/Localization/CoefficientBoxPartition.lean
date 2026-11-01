import PlanarNikodym.Analysis.Localization.ScaleTimePartition
import PlanarNikodym.Analysis.Fourier.LowerDegreePhaseScaling
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-! Unit-scale smooth covers of the expanding coefficient domain.
Only the finite index set grows; the window and all derivative constants
remain fixed. -/
noncomputable section
open Set
open scoped ContDiff Classical
namespace PlanarNikodym

def coefficientBoxWindow (m : ℕ) (x : Aux m) : ℝ := ∏ i, timePartitionWindow (x i)

theorem contDiff_coefficientBoxWindow (m : ℕ) : ContDiff ℝ ∞ (coefficientBoxWindow m) := by
  unfold coefficientBoxWindow
  apply contDiff_prod
  intro i _
  exact contDiff_timePartitionWindow.comp (contDiff_apply ℝ ℝ i)

theorem coefficientBoxWindow_nonneg (m : ℕ) (x : Aux m) : 0 ≤ coefficientBoxWindow m x :=
  Finset.prod_nonneg (fun _ _ => timePartitionWindow_nonneg _)

theorem coefficientBoxWindow_le_one (m : ℕ) (x : Aux m) : coefficientBoxWindow m x ≤ 1 :=
  Finset.prod_le_one (fun _ _ => timePartitionWindow_nonneg _) (fun _ _ => timePartitionWindow_le_one _)

theorem tsupport_coefficientBoxWindow_subset (m : ℕ) :
    tsupport (coefficientBoxWindow m) ⊆ {x | ∀ i, |x i| ≤ 1} := by
  apply closure_minimal ?_ ?_
  · intro x hx i
    by_contra hn
    have hzero : timePartitionWindow (x i) = 0 := by
      apply timePartitionWindow_eq_zero
      rcases lt_abs.mp (lt_of_not_ge hn) with h | h
      · exact Or.inr h.le
      · exact Or.inl (by linarith)
    exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
  · simpa only [setOf_forall] using isClosed_iInter (fun i : Fin m =>
      isClosed_le ((continuous_apply i : Continuous (fun x : Aux m => x i)).abs)
        (continuous_const : Continuous (fun _ : Aux m => (1 : ℝ))))

theorem hasCompactSupport_coefficientBoxWindow (m : ℕ) :
    HasCompactSupport (coefficientBoxWindow m) := by
  apply (isCompact_closedBall (0 : Aux m) 1).of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i => by
    simpa only [Real.norm_eq_abs] using tsupport_coefficientBoxWindow_subset m hx i)

def coefficientBoxCutoff {m : ℕ} (a : ℝ) (k : Fin m → ℕ) (x : Aux m) : ℝ :=
  coefficientBoxWindow m (x - fun i => a + (k i : ℝ))

theorem contDiff_coefficientBoxCutoff {m : ℕ} (a : ℝ) (k : Fin m → ℕ) :
    ContDiff ℝ ∞ (coefficientBoxCutoff a k) :=
  (contDiff_coefficientBoxWindow m).comp (contDiff_id.sub contDiff_const)

theorem tsupport_coefficientBoxCutoff_subset {m : ℕ} (a : ℝ) (k : Fin m → ℕ) :
    tsupport (coefficientBoxCutoff a k) ⊆ {x | ∀ i, |x i - a - (k i : ℝ)| ≤ 1} := by
  have hs := tsupport_comp_subset_preimage (coefficientBoxWindow m)
    (continuous_id.sub (continuous_const (y := fun i => a + (k i : ℝ))))
  intro x hx i
  have h := tsupport_coefficientBoxWindow_subset m (hs hx) i
  simpa only [Pi.sub_apply, sub_add_eq_sub_sub, id_eq] using h

theorem hasCompactSupport_coefficientBoxCutoff {m : ℕ} (a : ℝ) (k : Fin m → ℕ) :
    HasCompactSupport (coefficientBoxCutoff a k) := by
  apply (isCompact_closedBall (fun i => a + (k i : ℝ)) 1).of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs, sub_add_eq_sub_sub] using
    tsupport_coefficientBoxCutoff_subset a k hx i

/-- The number of closed unit-box supports meeting a coefficient point
is bounded independently of the expanding domain and of its scale. -/
theorem coefficientBoxCutoff_overlap_le {m : ℕ} (a : ℝ) (N : ℕ) (x : Aux m) :
    ((Fintype.piFinset (fun _ : Fin m => Finset.range N)).filter
      (fun k => x ∈ tsupport (coefficientBoxCutoff a k))).card ≤ 3 ^ m := by
  let J : Fin m → Finset ℤ := fun i => Finset.Icc (⌊x i - a⌋ - 1) (⌊x i - a⌋ + 1)
  have hmap : Set.MapsTo (fun k : Fin m → ℕ => fun i => (k i : ℤ))
      (↑((Fintype.piFinset (fun _ : Fin m => Finset.range N)).filter
        (fun k => x ∈ tsupport (coefficientBoxCutoff a k))) : Set (Fin m → ℕ))
      (↑(Fintype.piFinset J) : Set (Fin m → ℤ)) := by
    intro k hk
    apply Fintype.mem_piFinset.mpr
    intro i
    have h := (abs_le.mp (tsupport_coefficientBoxCutoff_subset a k
      (Finset.mem_filter.mp hk).2 i))
    have hfloor := Int.floor_le (x i - a)
    have hfloor' := Int.lt_floor_add_one (x i - a)
    have hlo : ((⌊x i - a⌋ : ℤ) : ℝ) - 1 ≤ (k i : ℝ) := by linarith
    have hhi : (k i : ℝ) < ((⌊x i - a⌋ : ℤ) : ℝ) + 2 := by linarith
    have hlo' : ⌊x i - a⌋ - 1 ≤ (k i : ℤ) := by exact_mod_cast hlo
    have hhi' : (k i : ℤ) < ⌊x i - a⌋ + 2 := by exact_mod_cast hhi
    change (k i : ℤ) ∈ J i
    exact Finset.mem_Icc.mpr ⟨hlo', by omega⟩
  have hcard := Finset.card_le_card_of_injOn _ hmap (fun k _ l _ h => by
    funext i
    exact Int.ofNat_injective (congrFun h i))
  have hJ : ∀ i, (J i).card = 3 := by
    intro i
    dsimp only [J]
    rw [Int.card_Icc, show ⌊x i - a⌋ + 1 + 1 - (⌊x i - a⌋ - 1) = (3 : ℤ) by ring]
    rfl
  simpa only [Fintype.card_piFinset, hJ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hcard

theorem exists_uniform_coefficientBoxCutoff_jet_bound (m j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a k x,
      ‖iteratedFDeriv ℝ j (@coefficientBoxCutoff m a k) x‖ ≤ C := by
  have hc := (hasCompactSupport_coefficientBoxWindow m).iteratedFDeriv (𝕜 := ℝ) j
  have ht := (contDiff_coefficientBoxWindow m).continuous_iteratedFDeriv (m := j) (by
    exact WithTop.coe_le_coe.mpr (show (j : ℕ∞) ≤ ⊤ from le_top))
  obtain ⟨x, hx⟩ := ht.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  refine ⟨‖iteratedFDeriv ℝ j (coefficientBoxWindow m) x‖, norm_nonneg _, ?_⟩
  intro a k y
  change ‖iteratedFDeriv ℝ j (fun z => coefficientBoxWindow m (z - fun i => a + (k i : ℝ))) y‖ ≤ _
  rw [iteratedFDeriv_comp_sub]
  exact hx _

theorem sum_coefficientBoxCutoff_eq_one {m : ℕ} (a : ℝ) (N : ℕ) (x : Aux m)
    (hx : ∀ i, x i ∈ Icc a (a + ((N : ℝ) - 1))) :
    ∑ k ∈ Fintype.piFinset (fun _ : Fin m => Finset.range N), coefficientBoxCutoff a k x = 1 := by
  have he : ∀ k, coefficientBoxCutoff a k x = ∏ i, scaleTimeCutoff a 1 (k i) (x i) := by
    intro k
    unfold coefficientBoxCutoff coefficientBoxWindow scaleTimeCutoff
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    simp [sub_add_eq_sub_sub]
  simp_rw [he]
  rw [Finset.sum_prod_piFinset (Finset.range N) (fun i k => scaleTimeCutoff a 1 k (x i))]
  apply Finset.prod_eq_one
  intro i _
  exact sum_scaleTimeCutoff_eq_one a zero_lt_one N (by simpa using hx i)

/-- Every compact transformed coefficient domain has an actual finite
unit-box partition. No a priori bound on its diameter is required. -/
theorem exists_coefficientBoxCutoff_partition {m : ℕ} {K : Set (Aux m)} (hK : IsCompact K) :
    ∃ a : ℝ, ∃ N : ℕ, ∀ x ∈ K,
      ∑ k ∈ Fintype.piFinset (fun _ : Fin m => Finset.range N), coefficientBoxCutoff a k x = 1 := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn : ContinuousOn id K)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * |R| + 1)
  refine ⟨-|R|, N, fun x hx => sum_coefficientBoxCutoff_eq_one _ _ _ ?_⟩
  intro i
  have hnorm : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hi : |x i| ≤ |R| := hnorm.trans ((hR x hx).trans (le_abs_self R))
  exact ⟨by linarith [(abs_le.mp hi).1], by linarith [(abs_le.mp hi).2]⟩

end PlanarNikodym
