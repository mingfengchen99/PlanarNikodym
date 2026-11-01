import PlanarNikodym.Analysis.Fourier.GlyzSmoothJetCoordinates
import PlanarNikodym.Analysis.Fourier.GlyzSmoothChartBounds
import PlanarNikodym.Geometry.SelectedCoordinateSplit
import PlanarNikodym.Analysis.Localization.CinematicTimeSlices

/-! Finite actual C∞ time-jet charts subordinate to a compact regular
cutoff. The partition may be evaluated at a frozen parent time so its
factors remain outside the input integral. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace PlanarNikodym

theorem Family.exists_glyz_uniform_smooth_moving_chart {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {t : ℝ} {v : Aux (d + 2)}
    (hdet : G.cinematicDet (t, parameterFrame d v) ≠ 0) (m : ℕ) (hm : m ≤ d + 2) :
    ∃ (σ : Fin m ↪ Fin (d + 2))
      (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux m)
        ((ℝ × Aux (d + 2)) × Aux m)) (K : Set ((ℝ × Aux (d + 2)) × Aux m)),
      IsCompact K ∧ ((t, v), (0 : Aux m)) ∈ interior K ∧ K ⊆ e.source ∧
      (∀ x, e x = (x.1, G.movingLowerJetMap hm σ x)) ∧
      (∀ x ∈ e.source, ContDiffAt ℝ ∞ e x) ∧
      (∀ x ∈ e.target, ContDiffAt ℝ ∞ e.symm x) ∧
      (∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∀ x ∈ K,
        b ≤ |fiberChartJacobian e x| ∧ |fiberChartJacobian e x| ≤ C) := by
  obtain ⟨σ, e, hx, _, he, hea, hei, _⟩ :=
    G.exists_movingLowerJet_smooth_chart hG hdet m hm univ univ_mem
  obtain ⟨K, hK, hxK, hKS⟩ := exists_compact_subset e.open_source hx
  exact ⟨σ, e, K, hK, hxK, hKS, he, hea, hei,
    exists_glyz_uniform_fiberChartJacobian_bounds e (fun x => by rw [he]) hea hei hK hKS⟩

/-- All charts and their compact domains are constructed from the
actual cinematic determinant. This requires C∞, not analyticity. -/
theorem Family.exists_glyz_smooth_moving_chart_partition {d m : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x)
    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0) (hm : m ≤ d + 2) :
    ∃ (S : Finset (tsupport χ)) (ψ : S → Cutoff d)
      (σ : S → (Fin m ↪ Fin (d + 2)))
      (e : S → OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux m)
        ((ℝ × Aux (d + 2)) × Aux m))
      (K : S → Set ((ℝ × Aux (d + 2)) × Aux m)),
      (∀ i, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧
        tsupport (ψ i) ⊆ tsupport χ ∧ (∀ x, 0 ≤ ψ i x ∧ ψ i x ≤ χ x) ∧
        IsCompact (K i) ∧ K i ⊆ (e i).source ∧
        (∀ x, e i x = (x.1, G.movingLowerJetMap hm (σ i) x)) ∧
        (∀ x ∈ (e i).source, ContDiffAt ℝ ∞ (e i) x) ∧
        (∀ x ∈ (e i).target, ContDiffAt ℝ ∞ (e i).symm x) ∧
        (∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∀ x ∈ K i,
          b ≤ |fiberChartJacobian (e i) x| ∧ |fiberChartJacobian (e i) x| ≤ C) ∧
        ∀ x ∈ tsupport (ψ i),
          selectedParameterLift (σ i) ((parameterFrame d).symm i.val.val.2) x ∈ K i) ∧
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
  have hcover : tsupport χ ⊆ ⋃ x : tsupport χ, U x := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨S, ψ, hψ, hsum⟩ := exists_finite_cutoff_partition χ hχ hc hχ0 U hU hcover
  refine ⟨S, ψ, (fun i => σ i.val), (fun i => e i.val), (fun i => K i.val), ?_, hsum⟩
  intro i
  obtain ⟨hi, hci, hsχ, hsU, hr⟩ := hψ i
  exact ⟨hi, hci, hsχ, hr, hK i.val, hKS i.val, he i.val, hea i.val, hei i.val,
    hJ i.val, fun x hx => interior_subset (hsU hx)⟩

/-- Smoothness suffices for continuity of the actual cinematic determinant. -/
theorem Family.continuous_cinematicDet_of_contDiff {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) :
    Continuous G.cinematicDet := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply (contDiff_timeDerivative (k := i) ?_).continuous
  exact (ContinuousLinearMap.apply ℝ ℝ
    ((0, parameterFrame d (Pi.single j 1)) : ℝ × Parameters 2 d)).contDiff.comp
      (hG.fderiv_right (by simp))

/-- A compact regular set has a single smooth cutoff which is one at
all sufficiently close frozen parent times. The threshold precedes all
input functions and frequency scales. -/
theorem Family.exists_glyz_frozen_time_cutoff {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0) :
    ∃ (χ : Cutoff d) (ε : ℝ), 0 < ε ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0) ∧
      ∀ x ∈ K, ∀ c : ℝ, |c - x.1| ≤ ε → χ (c, x.2) = 1 := by
  let U : Set (ℝ × Parameters 2 d) := {x | G.cinematicDet x ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage (G.continuous_cinematicDet_of_contDiff hG)
  obtain ⟨ε, L, hε, hL, _, hLU, hshift⟩ :=
    exists_compact_regular_time_neighborhood hK hU hdet
  obtain ⟨χ, V, hχ, hc, hr, _, hLV, hV1, hs⟩ := exists_compact_smooth_cutoff hL hU hLU
  refine ⟨χ, ε, hε, hχ, hc, hr, hs, ?_⟩
  intro x hx c hc
  apply hV1 _ (hLV ?_)
  simpa only [add_sub_cancel] using hshift x hx (c - x.1) hc

end PlanarNikodym
