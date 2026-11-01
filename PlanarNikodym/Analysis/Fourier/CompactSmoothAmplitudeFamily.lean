import PlanarNikodym.Analysis.Fourier.ComplexSymbolKernels
import PlanarNikodym.Analysis.Jets.CutoffGraphJetBounds

/-! A single genuine smooth compact joint amplitude determines a Schwartz
family with fixed compact support and all full derivatives uniformly
bounded over every frozen parameter. No compactness assumption on the
parameter space, or additional jet-bound hypothesis, is needed. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace PlanarNikodym

theorem hasCompactSupport_jointAmplitude_fiber
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {H : (Plane × Plane) × Q → ℂ} (hc : HasCompactSupport H) (q : Q) :
    HasCompactSupport (fun x : Plane × Plane => H (x, q)) := by
  apply HasCompactSupport.intro (hc.isCompact.image continuous_fst)
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (fun hy => hx ⟨(x, q), hy, rfl⟩)

def compactSmoothAmplitudeFamily
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (H : (Plane × Plane) × Q → ℂ) (hH : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) (q : Q) : SchwartzMap (Plane × Plane) ℂ :=
  (hasCompactSupport_jointAmplitude_fiber hc q).toSchwartzMap
    (hH.comp (contDiff_id.prodMk contDiff_const))

@[simp] theorem compactSmoothAmplitudeFamily_apply
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (H : (Plane × Plane) × Q → ℂ) (hH : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) (q : Q) (x : Plane × Plane) :
    compactSmoothAmplitudeFamily H hH hc q x = H (x, q) := rfl

theorem tsupport_compactSmoothAmplitudeFamily_subset
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (H : (Plane × Plane) × Q → ℂ) (hH : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) (q : Q) :
    tsupport (compactSmoothAmplitudeFamily H hH hc q) ⊆ Prod.fst '' tsupport H := by
  apply closure_minimal _ (hc.isCompact.image continuous_fst).isClosed
  intro x hx
  exact ⟨(x, q), subset_closure hx, rfl⟩

/-- The joint function of the actual fibre jets vanishes outside the
joint support of `H`, even though the parameter space is unrestricted. -/
theorem hasCompactSupport_jointAmplitude_fiberJet
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {H : (Plane × Plane) × Q → ℂ} (hc : HasCompactSupport H) (j : ℕ) :
    HasCompactSupport (fun y : (Plane × Plane) × Q =>
      iteratedFDeriv ℝ j (fun x => H (x, y.2)) y.1) := by
  apply HasCompactSupport.intro hc.isCompact
  intro y hy
  have hz : (fun x : Plane × Plane => H (x, y.2)) =ᶠ[𝓝 y.1] 0 :=
    (notMem_tsupport_iff_eventuallyEq.mp hy).comp_tendsto
      (continuous_id.prodMk continuous_const).continuousAt
  have he := (hz.iteratedFDeriv ℝ j).self_of_nhds
  simpa only [Pi.zero_def, iteratedFDeriv_fun_zero] using he

theorem exists_uniform_compactSmoothAmplitudeFamily_jet_bound
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (H : (Plane × Plane) × Q → ℂ) (hH : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q x,
      ‖iteratedFDeriv ℝ j (compactSmoothAmplitudeFamily H hH hc q) x‖ ≤ C := by
  let J := fun y : (Plane × Plane) × Q => iteratedFDeriv ℝ j (fun x => H (x, y.2)) y.1
  have hJ : Continuous J := continuous_iff_continuousAt.mpr fun y =>
    (contDiffAt_fiber_iteratedFDeriv j (hH.contDiffAt (x := y))).continuousAt
  obtain ⟨y₀, hy₀⟩ := hJ.norm.exists_forall_ge_of_hasCompactSupport
    (hasCompactSupport_jointAmplitude_fiberJet hc j).norm
  exact ⟨‖J y₀‖, norm_nonneg _, fun q x => hy₀ (x, q)⟩

/-- The directly constructed compact support and jet bounds required by
uniform Fourier-coefficient estimates, with quantifiers over all `q`. -/
theorem compactSmoothAmplitudeFamily_uniform_support_and_jets
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (H : (Plane × Plane) × Q → ℂ) (hH : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) :
    IsCompact (Prod.fst '' tsupport H) ∧
      (∀ q, tsupport (compactSmoothAmplitudeFamily H hH hc q) ⊆ Prod.fst '' tsupport H) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q x,
        ‖iteratedFDeriv ℝ j (compactSmoothAmplitudeFamily H hH hc q) x‖ ≤ C) :=
  ⟨hc.isCompact.image continuous_fst,
    tsupport_compactSmoothAmplitudeFamily_subset H hH hc,
    exists_uniform_compactSmoothAmplitudeFamily_jet_bound H hH hc⟩

end PlanarNikodym
