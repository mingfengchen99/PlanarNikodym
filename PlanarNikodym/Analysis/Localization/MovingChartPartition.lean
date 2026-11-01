import PlanarNikodym.Analysis.Fourier.MovingCinematicBounds
import PlanarNikodym.Geometry.SelectedCoordinateSplit
import PlanarNikodym.Analysis.Localization.CinematicTimeSlices

/-! Actual finite moving-coordinate localization of the original cutoff.
One common positive scale threshold keeps all relevant centers and time
segments in compact joint charts with uniform inverse-jet constants. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace PlanarNikodym

theorem Family.exists_finite_movingChart_cutoff_partition {d m : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x)
    (ha : ∀ x ∈ tsupport χ, AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
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
        AnalyticOnNhd ℝ (e i) (e i).source ∧ AnalyticOnNhd ℝ (e i).symm (e i).target ∧
        (∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∀ x ∈ K i,
          b ≤ |fiberChartJacobian (e i) x| ∧ |fiberChartJacobian (e i) x| ≤ C) ∧
        (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
          (∀ x ∈ K i, ‖iteratedFDeriv ℝ j (e i) x‖ ≤ C) ∧
          ∀ y ∈ e i '' K i, ‖iteratedFDeriv ℝ j (e i).symm y‖ ≤ C) ∧
        IsCompact (L i) ∧ tsupport (ψ i) ⊆ L i ∧
        (∀ x ∈ L i, selectedParameterLift (σ i) ((parameterFrame d).symm i.val.val.2) x ∈ K i) ∧
        (∀ x ∈ L i, AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x) ∧
        ∀ (a δ : ℝ), 0 < δ → δ ≤ ε / 2 → ∀ (j : ℕ) (x : ℝ × Parameters 2 d),
          x ∈ tsupport (scaleTimeLocalizedCutoff (ψ i) a δ j) →
          ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ s ∈ uIcc (a + (j : ℝ) * δ) (a + (j : ℝ) * δ + δ * τ),
            (s, x.2) ∈ L i) ∧
      ∀ x, ∑ i : S, ψ i x = χ x := by
  classical
  have hlocal (x : tsupport χ) := G.exists_uniform_movingLowerJet_chart
    (t := x.val.1) (v := (parameterFrame d).symm x.val.2)
    (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using ha x x.property)
    (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hdet x x.property) m hm
  choose σ e K T hK hT hxK hKS hTe hTS he hea hei hJ hj hreg using hlocal
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
    hJ i.val, ?_, hL i, hψL i, ?_, ?_, ?_⟩
  · intro j
    simpa only [hTe i.val] using hj i.val j
  · intro x hx
    exact interior_subset (hLU i hx)
  · intro x hx
    have hLift := interior_subset (hLU i hx)
    have h := hreg i.val _ (hKS i.val hLift)
    change AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2)
      (x.1, parameterFrame d ((selectedParameterLift (σ i.val) ((parameterFrame d).symm i.val.val.2) x).1.2 +
        coordinateInsertion (σ i.val) (selectedParameterLift (σ i.val) ((parameterFrame d).symm i.val.val.2) x).2)) at h
    rw [selectedParameterLift_reconstruct] at h
    exact h
  · intro a δ hδ hδr j x hx τ hτ s hs
    exact htime i a δ hδ (hδr.trans (by linarith [hrε i])) j x hx τ hτ s hs

end PlanarNikodym
