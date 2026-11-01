import PlanarNikodym.Projection.FiniteFanRefinement

/-! Compact selection from actual local finite fans.

The initial positive target, each compact refinement, the decreasing
intersection, and its two projection integrals are constructed here.
The finite geometric replacement is the sole local construction used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace PlanarNikodym

/-- An actual local finite-fan construction, on every open subset of a
transverse parameter domain, produces a compact set with zero curve
projection integral and positive centre projection integral. -/
theorem exists_compact_zero_positive_projection_of_local_fans
    (φ ψ : ℝ → Plane → ℝ) {J X : Set ℝ} {U : Set Plane}
    (hJ : MeasurableSet J) (hJfinite : volume J < ∞)
    (hX : IsOpen X) (hU : IsOpen U) (hXn : X.Nonempty) (hUn : U.Nonempty)
    (hφ : ContinuousOn (fun p : ℝ × Plane => φ p.1 p.2) (J ×ˢ U))
    (hψ : ContinuousOn (fun p : ℝ × Plane => ψ p.1 p.2) (X ×ˢ U))
    (v : Plane)
    (hf : ∀ x ∈ X, ∀ q ∈ U, DifferentiableAt ℝ (ψ x) q)
    (hd : ∀ x ∈ X, ∀ q ∈ U, 0 < fderiv ℝ (ψ x) q v)
    (hfan : ∀ W : Set Plane, IsOpen W → W ⊆ U →
      ∀ (c : Plane) (a : ℝ), 0 < a → centeredBlindSegment c v a ⊆ W →
      ∀ e : ℝ, 0 < e →
        ∃ L : Set Plane, IsCompact L ∧ L ⊆ W ∧
          (∀ x ∈ X, ψ x '' centeredBlindSegment c v a ⊆ ψ x '' interior L) ∧
          ∀ t ∈ J, volume (φ t '' L) ≤ ENNReal.ofReal e) :
    ∃ G : Set Plane, IsCompact G ∧ MeasurableSet G ∧ G.Nonempty ∧ G ⊆ U ∧
      (∫⁻ t in J, volume (φ t '' G)) = 0 ∧
      0 < ∫⁻ x in X, volume (ψ x '' G) := by
  obtain ⟨K₀, F, hK₀, hK₀U, hF, hFpos, hinit⟩ :=
    exists_compact_positive_interior_projection_target ψ hX hU hXn hUn hψ v hf hd
  have hfanIntegral :
      ∀ W : Set Plane, IsOpen W → W ⊆ U →
      ∀ (c : Plane) (a : ℝ), 0 < a → a < 1 → centeredBlindSegment c v a ⊆ W →
      ∀ e : ℝ≥0∞, 0 < e →
        ∃ L : Set Plane, IsCompact L ∧ L ⊆ W ∧
          (∀ x ∈ X, ψ x '' centeredBlindSegment c v a ⊆ ψ x '' interior L) ∧
          (∫⁻ t in J, volume (φ t '' L)) ≤ e := by
    intro W hW hWU c a ha _ hseg e he
    obtain ⟨ε, hε, hbound⟩ :=
      exists_uniform_scalarProjection_integral_tolerance hJ hJfinite he
    obtain ⟨L, hL, hLW, hretain, hsmall⟩ := hfan W hW hWU c a ha hseg ε hε
    exact ⟨L, hL, hLW, hretain, hbound _ hsmall⟩
  have hstep : ∀ K : Set Plane, IsCompact K → K ⊆ U →
      F ⊆ scalarProjectionSweep ψ X (interior K) →
      ∀ δ : ℝ≥0∞, 0 < δ →
        ∃ L : Set Plane, IsCompact L ∧ L ⊆ interior K ∧
          F ⊆ scalarProjectionSweep ψ X (interior L) ∧
          (∫⁻ t in J, volume (φ t '' L)) ≤ δ := by
    intro K _ hKU hFK δ hδ
    exact exists_interior_projection_refinement_of_local_fans φ ψ
      hJ hX hKU hF hFK hφ hψ v hf hd (by norm_num : (0 : ℝ) < 1)
      hfanIntegral δ hδ
  let ε : ℕ → ℝ≥0∞ := fun n => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    exact ENNReal.inv_pos.mpr (by simp)
  have hε : Tendsto ε atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hψslice : ∀ x ∈ X, ContinuousOn (ψ x) U := by
    intro x hx q hq
    exact (hf x hx q hq).continuousAt.continuousWithinAt
  obtain ⟨G, hGc, hGm, hGn, hGK, _, hG0, hGpos⟩ :=
    exists_compact_prescribedProjection_of_interior_refinement φ ψ J X
      hX.measurableSet U K₀ F hK₀ hK₀U hF hFpos hinit hψslice ε hεpos hε hstep
  exact ⟨G, hGc, hGm, hGn, hGK.trans hK₀U, hG0, hGpos⟩

end PlanarNikodym
