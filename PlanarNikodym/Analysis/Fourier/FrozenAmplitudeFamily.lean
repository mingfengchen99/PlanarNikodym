import PlanarNikodym.Analysis.Fourier.VariablePhaseFreezing
import PlanarNikodym.Analysis.Fourier.UniformFourierMoments

/-! The actual amplitude produced by spatial phase freezing is a uniformly
bounded compact Schwartz family in its input variables. Smoothness and
compact support of the original amplitude construct all required derivative
bounds, so no Fourier-coefficient estimate is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform
namespace PlanarNikodym

/-- Compact parameter sets and fixed compact fiber support yield full
uniform fiber-jet bounds for a genuine jointly smooth function. -/
theorem exists_uniform_compact_parameter_fiber_jet_bound
    {V Q : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {H : V × Q → ℂ} (hH : ContDiff ℝ ∞ H)
    {J : Set V} (hJ : IsCompact J) {K : Set Q} (hK : IsCompact K)
    (hs : ∀ q ∈ K, tsupport (fun x => H (x, q)) ⊆ J) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => H (y, q)) x‖ ≤ C := by
  have hc : Continuous (fun z : V × Q =>
      iteratedFDeriv ℝ j (fun y => H (y, z.2)) z.1) :=
    continuous_iff_continuousAt.mpr fun _ =>
      (contDiffAt_fiber_iteratedFDeriv j hH.contDiffAt).continuousAt
  obtain ⟨B, hB⟩ := (hJ.prod hK).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B|, abs_nonneg _, fun q hq x => ?_⟩
  by_cases hx : x ∈ J
  · exact (hB (x, q) ⟨hx, hq⟩).trans (le_abs_self B)
  · have hz : iteratedFDeriv ℝ j (fun y => H (y, q)) x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hi => hx (hs q hq
        (tsupport_iteratedFDeriv_subset j hi))
    rw [hz, norm_zero]
    exact abs_nonneg _

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def frozenSpatialAmplitude (a : E × Plane → ℂ) (Φ : E × ℝ → ℝ)
    (q : Plane × (E × E) × ℝ × ℝ) : ℂ :=
  a (q.2.1.1 + q.2.2.2 • q.2.1.2, q.1) *
    spatialPhaseCorrection Φ (((q.2.1.1, q.2.1.2, q.1.1), q.1.2), q.2.2)

theorem contDiff_frozenSpatialAmplitude [FiniteDimensional ℝ E]
    {a : E × Plane → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : E × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (frozenSpatialAmplitude a Φ) := by
  have ha' : ContDiff ℝ ∞ (fun q : Plane × (E × E) × ℝ × ℝ =>
      a (q.2.1.1 + q.2.2.2 • q.2.1.2, q.1)) := ha.comp (by fun_prop)
  exact ha'.mul ((contDiff_spatialPhaseCorrection hΦ).comp (by fun_prop))

theorem tsupport_frozenSpatialAmplitude_subset {a : E × Plane → ℂ}
    (hc : HasCompactSupport a) (Φ : E × ℝ → ℝ) (q : (E × E) × ℝ × ℝ) :
    tsupport (fun x => frozenSpatialAmplitude a Φ (x, q)) ⊆ Prod.snd '' tsupport a := by
  apply closure_minimal _ (hc.isCompact.image continuous_snd).isClosed
  intro x hx
  have ha : a (q.1.1 + q.2.2 • q.1.2, x) ≠ 0 := by
    intro hz
    exact hx (by simp [frozenSpatialAmplitude, hz])
  exact ⟨(q.1.1 + q.2.2 • q.1.2, x), subset_closure ha, rfl⟩

def frozenSpatialAmplitudeSchwartz [FiniteDimensional ℝ E]
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (q : (E × E) × ℝ × ℝ) :
    SchwartzMap Plane ℂ :=
  HasCompactSupport.toSchwartzMap
    ((hc.isCompact.image continuous_snd).of_isClosed_subset
      (isClosed_tsupport _)
      (tsupport_frozenSpatialAmplitude_subset hc Φ q))
      ((contDiff_frozenSpatialAmplitude ha hΦ).comp (contDiff_id.prodMk contDiff_const))

@[simp] theorem frozenSpatialAmplitudeSchwartz_apply [FiniteDimensional ℝ E]
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (q : (E × E) × ℝ × ℝ) (x : Plane) :
    frozenSpatialAmplitudeSchwartz a ha hc Φ hΦ q x = frozenSpatialAmplitude a Φ (x, q) := rfl

/-- Derivative constants are obtained from the original smooth amplitude
and the exact Taylor correction over one fixed compact parameter set. -/
theorem frozenSpatialAmplitude_uniform_support_and_jets [FiniteDimensional ℝ E]
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set (E × E)} (hK : IsCompact K) :
    (∀ q, tsupport (frozenSpatialAmplitudeSchwartz a ha hc Φ hΦ q) ⊆
      Prod.snd '' tsupport a) ∧
    (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q : (E × E) × ℝ × ℝ,
      q.1 ∈ K → q.2.1 ∈ Icc (0 : ℝ) 1 → q.2.2 ∈ Icc (0 : ℝ) 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (frozenSpatialAmplitudeSchwartz a ha hc Φ hΦ q) x‖ ≤ C) := by
  refine ⟨tsupport_frozenSpatialAmplitude_subset hc Φ, fun j => ?_⟩
  obtain ⟨C, hC, hb⟩ := exists_uniform_compact_parameter_fiber_jet_bound
    (contDiff_frozenSpatialAmplitude ha hΦ) (hc.isCompact.image continuous_snd)
    (hK.prod (isCompact_Icc.prod isCompact_Icc))
    (fun q _ => tsupport_frozenSpatialAmplitude_subset hc Φ q) j
  exact ⟨C, hC, fun q hq hα hδ x => hb q ⟨hq, hα, hδ⟩ x⟩

end PlanarNikodym
