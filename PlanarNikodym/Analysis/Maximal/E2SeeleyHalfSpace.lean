import PlanarNikodym.Analysis.Maximal.E2SeeleyJetMoments
import PlanarNikodym.Analysis.Maximal.E2SeeleyClosedSeries
import PlanarNikodym.Analysis.Maximal.E2SeeleyJetGluing

/-! The actual Seeley extension on a closed half space. Every reflection
coefficient and node is constructed in the preceding modules. -/
noncomputable section
open Set
open scoped ContDiff
namespace PlanarNikodym
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def e2SeeleyNegative (f : (ℝ × E) → F) (x : ℝ × E) : F :=
  ∑' i : E2SeeleyIndex, e2SeeleyA i • f (e2TimeDilation E (e2SeeleyB i) x)

def e2SeeleyNegativeJets (p : (ℝ × E) → FormalMultilinearSeries ℝ (ℝ × E) F)
    (x : ℝ × E) (m : ℕ) :=
  ∑' i : E2SeeleyIndex, e2SeeleyA i •
    (p (e2TimeDilation E (e2SeeleyB i) x) m).compContinuousLinearMap
      (fun _ => e2TimeDilation E (e2SeeleyB i))

theorem e2_hasFTaylorSeries_seeley_negative
    {f : (ℝ × E) → F} {p : (ℝ × E) → FormalMultilinearSeries ℝ (ℝ × E) F}
    (hp : HasFTaylorSeriesUpToOn ∞ f p (e2PositiveHalfSpace E))
    (M : ℕ → ℝ) (hM : ∀ m, 0 ≤ M m)
    (hb : ∀ m x, x ∈ e2PositiveHalfSpace E → ‖p x m‖ ≤ M m) :
    HasFTaylorSeriesUpToOn ∞ (e2SeeleyNegative f) (e2SeeleyNegativeJets p)
      (e2NegativeHalfSpace E) := by
  let A := fun i : E2SeeleyIndex => e2TimeDilation E (e2SeeleyB i)
  let fi := fun i : E2SeeleyIndex => fun x => e2SeeleyA i • f (A i x)
  let pi := fun i : E2SeeleyIndex => fun x m => e2SeeleyA i •
    (p (A i x) m).compContinuousLinearMap (fun _ => A i)
  have hpi (i : E2SeeleyIndex) :
      HasFTaylorSeriesUpToOn ∞ (fi i) (pi i) (e2NegativeHalfSpace E) := by
    have hh := (hp.compContinuousLinearMap (A i)).continuousLinearMap_comp
      (e2SeeleyA i • ContinuousLinearMap.id ℝ F)
    have hs : (A i) ⁻¹' e2PositiveHalfSpace E = e2NegativeHalfSpace E :=
      e2TimeDilation_preimage_half E (e2SeeleyB_neg i)
    rw [hs] at hh
    convert hh using 1
    · funext x
      rfl
    · funext x m
      ext v
      rfl
  have hv (m : ℕ) :
      Summable (fun i : E2SeeleyIndex => M m * (|e2SeeleyA i| * |e2SeeleyB i| ^ m)) :=
    (e2Seeley_summable_absolute_moment m).mul_left (M m)
  have hbound (m : ℕ) (i : E2SeeleyIndex) (x : ℝ × E)
      (hx : x ∈ e2NegativeHalfSpace E) :
      ‖pi i x m‖ ≤ M m * (|e2SeeleyA i| * |e2SeeleyB i| ^ m) := by
    have hax : A i x ∈ e2PositiveHalfSpace E := by
      rw [← e2TimeDilation_preimage_half E (e2SeeleyB_neg i)] at hx
      exact hx
    have hn : ‖A i‖ ≤ |e2SeeleyB i| := e2TimeDilation_norm_le E (e2SeeleyB_abs_ge_one i)
    calc
      ‖pi i x m‖ = |e2SeeleyA i| *
          ‖(p (A i x) m).compContinuousLinearMap (fun _ => A i)‖ := by
        simp only [pi, norm_smul, Real.norm_eq_abs]
      _ ≤ |e2SeeleyA i| * (‖p (A i x) m‖ * ∏ _ : Fin m, ‖A i‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) (abs_nonneg _)
      _ ≤ |e2SeeleyA i| * (M m * |e2SeeleyB i| ^ m) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul (hb m (A i x) hax) (pow_le_pow_left₀ (norm_nonneg _) hn m)
          (by positivity) (hM m)
      _ = _ := by ring
  exact e2_hasFTaylorSeries_tsum_closed_convex (e2NegativeHalfSpace_convex E)
    (e2NegativeHalfSpace_closure_interior E) fi pi hpi _ hv hbound

omit [CompleteSpace F] in
theorem e2_seeley_boundary_jets
    (p : (ℝ × E) → FormalMultilinearSeries ℝ (ℝ × E) F)
    (x : ℝ × E) (hx : x.1 = 0) : e2SeeleyNegativeJets p x = p x := by
  funext m
  have hh (i : E2SeeleyIndex) : e2TimeDilation E (e2SeeleyB i) x = x := by
    ext <;> simp [hx]
  simp only [e2SeeleyNegativeJets, hh]
  exact e2_seeley_full_jet_moment _

def e2SeeleyExtension (f : (ℝ × E) → F) : (ℝ × E) → F :=
  by
    classical
    exact (e2PositiveHalfSpace E).piecewise f (e2SeeleyNegative f)

omit [CompleteSpace F] in
theorem e2SeeleyExtension_eq {f : (ℝ × E) → F} {x : ℝ × E}
    (hx : x ∈ e2PositiveHalfSpace E) : e2SeeleyExtension f x = f x := by
  classical
  simp [e2SeeleyExtension, hx]

theorem e2SeeleyExtension_contDiff
    {f : (ℝ × E) → F} {p : (ℝ × E) → FormalMultilinearSeries ℝ (ℝ × E) F}
    (hp : HasFTaylorSeriesUpToOn ∞ f p (e2PositiveHalfSpace E))
    (M : ℕ → ℝ) (hM : ∀ m, 0 ≤ M m)
    (hb : ∀ m x, x ∈ e2PositiveHalfSpace E → ‖p x m‖ ≤ M m) :
    ContDiff ℝ ∞ (e2SeeleyExtension f) := by
  classical
  apply e2_contDiff_piecewise_of_matching_closed_jets (e2PositiveHalfSpace_isClosed E)
    (e2NegativeHalfSpace_isClosed E) (e2HalfSpaces_cover E) hp
    (e2_hasFTaylorSeries_seeley_negative hp M hM hb)
  intro x hx
  have hz : x.1 = 0 := le_antisymm hx.2.1 hx.1.1
  exact (e2_seeley_boundary_jets p x hz).symm

end PlanarNikodym
