import PlanarNikodym.Analysis.Fourier.GlyzSmoothMovingAtlas
import PlanarNikodym.Geometry.SelectedCoordinateSplit
import PlanarNikodym.Analysis.Localization.CinematicTimeSlices

/-! Genuine C∞ moving-chart localization of the original cutoff.
A common positive threshold keeps every active time segment inside the
constructed compact chart domains; no analytic regularity is required. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace PlanarNikodym

theorem Family.exists_e3_smooth_movingChart_cutoff_partition {d m : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x)
    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0) (hm : m ≤ d + 2) :
    ∃ (S : Finset (tsupport χ)) (ψ : S → Cutoff d)
      (σ : S → (Fin m ↪ Fin (d + 2)))
      (e : S → OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux m)
        ((ℝ × Aux (d + 2)) × Aux m))
      (K : S → Set ((ℝ × Aux (d + 2)) × Aux m))
      (L : S → Set (ℝ × Parameters 2 d)) (ε : ℝ), 0 < ε ∧
      (∀ i, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧
        tsupport (ψ i) ⊆ tsupport χ ∧ (∀ x, 0 ≤ ψ i x ∧ ψ i x ≤ χ x) ∧
        IsCompact (K i) ∧ K i ⊆ (e i).source ∧
        (∀ x, e i x = (x.1, G.movingLowerJetMap hm (σ i) x)) ∧
        (∀ x ∈ (e i).source, ContDiffAt ℝ ∞ (e i) x) ∧
        (∀ x ∈ (e i).target, ContDiffAt ℝ ∞ (e i).symm x) ∧
        (∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∀ x ∈ K i,
          b ≤ |fiberChartJacobian (e i) x| ∧ |fiberChartJacobian (e i) x| ≤ C) ∧
        IsCompact (L i) ∧ tsupport (ψ i) ⊆ L i ∧
        (∀ x ∈ L i, selectedParameterLift (σ i) ((parameterFrame d).symm i.val.val.2) x ∈ K i) ∧
        (∀ x ∈ L i, ContDiffAt ℝ ∞ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x) ∧
        ∀ (a δ : ℝ), 0 < δ → δ ≤ ε / 2 → ∀ (j : ℕ) (x : ℝ × Parameters 2 d),
          x ∈ tsupport (scaleTimeLocalizedCutoff (ψ i) a δ j) →
          ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ s ∈ uIcc (a + (j : ℝ) * δ) (a + (j : ℝ) * δ + δ * τ),
            (s, x.2) ∈ L i) ∧
      ∀ x, ∑ i : S, ψ i x = χ x := by
  classical
  have hlocal (x : tsupport χ) := G.exists_glyz_uniform_smooth_moving_chart hG
    (t := x.val.1) (v := (parameterFrame d).symm x.val.2)
    (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hdet x x.property) m hm
  choose σ e K hK hxK hKS he hea hei hJ using hlocal
  let U : tsupport χ → Set (ℝ × Parameters 2 d) := fun x =>
    selectedParameterLift (σ x) ((parameterFrame d).symm x.val.2) ⁻¹' interior (K x)
  have hU (x : tsupport χ) : IsOpen (U x) :=
    isOpen_interior.preimage (continuous_selectedParameterLift _ _)
  have hxU (x : tsupport χ) : x.val ∈ U x := by
    change selectedParameterLift (σ x) ((parameterFrame d).symm x.val.2) x.val ∈ interior (K x)
    have hx : selectedParameterLift (σ x) ((parameterFrame d).symm x.val.2) x.val =
        ((x.val.1, (parameterFrame d).symm x.val.2), 0) := by
      simpa only [ContinuousLinearEquiv.apply_symm_apply, Prod.mk.eta] using
        selectedParameterLift_self (σ x) ((parameterFrame d).symm x.val.2) x.val.1
    rw [hx]
    exact hxK x
  have hcover : tsupport χ ⊆ ⋃ x : tsupport χ, U x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨S, ψ, hψ, hsum⟩ := exists_finite_cutoff_partition χ hχ hc hχ0 U hU hcover
  have hspan (i : S) := exists_regular_scaleTimeLocalized_segments (ψ i)
    (hψ i).2.1 (hU i.val) (hψ i).2.2.2.1
  choose ε L hε hL hψL hLU htime using hspan
  obtain ⟨r, hr, hrε⟩ := exists_common_time_scale_bound ε hε
  refine ⟨S, ψ, (fun i => σ i.val), (fun i => e i.val), (fun i => K i.val), L, r, hr, ?_, hsum⟩
  intro i
  obtain ⟨hi, hci, hsχ, _, hbound⟩ := hψ i
  refine ⟨hi, hci, hsχ, hbound, hK i.val, hKS i.val, he i.val, hea i.val, hei i.val,
    hJ i.val, hL i, hψL i, ?_, ?_, ?_⟩
  · intro x hx
    exact interior_subset (hLU i hx)
  · intro x _hx
    exact hG.contDiffAt
  · intro a δ hδ hδr j x hx τ hτ s hs
    exact htime i a δ hδ (hδr.trans (by linarith [hrε i])) j x hx τ hτ s hs

end PlanarNikodym
