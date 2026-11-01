import PlanarNikodym.Analysis.Fourier.E3SmoothPartialExtensionL2
import PlanarNikodym.Analysis.Fourier.GlyzSmoothChartBounds
import PlanarNikodym.Analysis.Fourier.SelectedSliceSupport

/-! The actual moving chart of A4.2 now gives the complete main-piece
L² square sum on the full selected-parameter plane. All pure chart
conditions are constructed here; the compact amplitude and symbol
constants precede every time center, frozen parameter, input and scale. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

theorem Family.exists_e3_uniform_movingChart_main_square_sum_bound {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (hm : 2 ≤ d + 2) (σ : Fin 2 ↪ Fin (d + 2))
    (E : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2))
    (he : ∀ x, E x = (x.1, G.movingLowerJetMap hm σ x))
    (hea : ∀ x ∈ E.source, ContDiffAt ℝ ∞ E x) (hei : ∀ x ∈ E.target, ContDiffAt ℝ ∞ E.symm x)
    (ψ : Cutoff d) (hψ : ContDiff ℝ ∞ ψ)
    {K : Set ((ℝ × Aux (d + 2)) × Aux 2)} (hK : IsCompact K) (hKS : K ⊆ E.source)
    {β : ℝ} (hβ : 0 < β) (hJac : ∀ x ∈ K, β ≤ |fiberChartJacobian E x|)
    (L : Set (ℝ × Parameters 2 d)) (_hL : IsCompact L)
    (v₀ : Aux (d + 2)) (hLift : ∀ x ∈ L, selectedParameterLift σ v₀ x ∈ K)
    (ε : ℝ) (_hε : 0 < ε)
    (hspan : ∀ (b δ : ℝ), 0 < δ → δ ≤ ε / 2 → ∀ i : ℕ,
      ∀ x ∈ tsupport (scaleTimeLocalizedCutoff ψ b δ i),
        ∀ τ ∈ Icc (-1 : ℝ) 1,
          ∀ s ∈ uIcc (b + (i : ℝ) * δ) (b + (i : ℝ) * δ + δ * τ), (s, x.2) ∈ L)
    (F : FrequencyCutoff) (βfreq : ℝ → ℝ) (hβfreq : Continuous βfreq) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
      (∀ ξ : Plane, |F.bandSymbol 0 ξ * βfreq ξ.2| ≤ M) ∧
      ∀ (b δ : ℝ) (N : ℕ) (u : UnselectedCoordinates σ)
        (f : Plane → ℂ), Integrable f → MemLp f 2 volume →
      ∀ κ r : ℝ, 0 < κ → 0 < r → 0 < δ → δ ≤ 1 → δ ≤ ε / 2 →
      (2 * Real.pi * r) * δ ^ (2 : ℕ) ∈ Icc (0 : ℝ) 1 →
      (∀ ξ : Plane, |ξ.2| < κ → F.bandSymbol 0 ξ * βfreq ξ.2 = 0) →
      ENNReal.ofReal β * (∑ i ∈ Finset.range N, ∫⁻ z : Aux 2,
        ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff ψ b δ i) F βfreq r f
          (parameterFrame d ((v₀ + selectedCoordinateSplit σ (0, u)) +
            coordinateInsertion σ z))‖ₑ ^ (2 : ℕ)) ≤
        (3 : ℝ≥0∞) * ENNReal.ofReal (C ^ (2 : ℕ) * M ^ (2 : ℕ) * κ⁻¹ * r⁻¹) *
          ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  have hT : IsCompact (E '' K) := hK.image_of_continuousOn (E.continuousOn.mono hKS)
  have hTE : E '' K ⊆ E.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact E.map_source (hKS hx)
  obtain ⟨C, M, hC, hM, hmBound, hmain⟩ :=
    G.exists_e3_uniform_cutoffPartialExtension_square_sum_bound hG E hei σ ψ hψ F βfreq hβfreq hT hTE
  refine ⟨C, M, hC, hM, hmBound, ?_⟩
  intro b δ N u f hf1 hf2 κ r hκ hr hδ hδ1 hδε hα hgap
  let v : Aux (d + 2) := v₀ + selectedCoordinateSplit σ (0, u)
  have hfirst : ∀ x, (E x).1 = x.1 := fun x => by rw [he]
  let e := fun i : ℕ => retainedParameterFiber E hfirst (b + (i : ℝ) * δ, v)
  let A := fun i : ℕ => {z : Aux 2 | ((b + (i : ℝ) * δ, v), z) ∈ K}
  have hgeom : E3TimeSliceChartGeometry G E σ (E '' K) b δ N β (fun _ => v) e A hm := by
    intro i _hi
    let q : ℝ × Aux (d + 2) := (b + (i : ℝ) * δ, v)
    have heFiber : ∀ z, e i z = G.lowerCinematicJetMap hm σ q.1 q.2 z := by
      intro z
      change (E (q, z)).2 = _
      rw [he]
      rfl
    refine ⟨heFiber, (glyz_retainedParameterFiber_smooth E hfirst hea hei q).1,
      hK.isClosed.measurableSet.preimage (continuous_const.prodMk continuous_id).measurable,
      fun z hz => hKS hz, ?_, ?_, ?_⟩
    · intro z hz
      exact hJac (q, z) hz
    · rintro y ⟨z, hz, rfl⟩
      exact ⟨(q, z), hz, Prod.ext (hfirst (q, z)) rfl⟩
    · intro y _hy
      rfl
  have hbound := hmain b δ N (fun _ => v) e A hm β hβ.le hgeom f hf1 hf2
    κ r hκ hr hδ hδ1 hα hgap
  have hcenter (i : ℕ) : ∀ x ∈ tsupport (scaleTimeLocalizedCutoff ψ b δ i),
      (b + (i : ℝ) * δ, x.2) ∈ L := by
    intro x hx
    exact hspan b δ hδ hδε i x hx 0 (by norm_num) _ left_mem_uIcc
  have heq : (∑ i ∈ Finset.range N, ∫⁻ z : Aux 2,
      ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff ψ b δ i) F βfreq r f
        (parameterFrame d (v + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ)) =
      ∑ i ∈ Finset.range N, ∫⁻ z in A i,
      ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff ψ b δ i) F βfreq r f
        (parameterFrame d (v + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro i _hi
    exact G.lintegral_cutoffPartialExtension_selected_eq_restrict ψ σ v₀ hK L hLift
      b i (hcenter i) u F βfreq f r
  change ENNReal.ofReal β * _ ≤ _
  rw [heq]
  exact hbound

end PlanarNikodym
