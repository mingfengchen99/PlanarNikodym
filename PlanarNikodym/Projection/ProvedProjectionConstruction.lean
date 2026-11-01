import PlanarNikodym.Projection.UniformSmallProjectionFan
import PlanarNikodym.Projection.LocalTransverseProjectionData
import PlanarNikodym.Projection.LocalFanCompactSelection
import PlanarNikodym.Projection.ProjectionInputs

/-! The actual scalar projection construction.

The local analytic data, finite Venetian blinds, common positive
thickening, positive compact target, and nested compact limit are
assembled here. Both branches of the original scalar model are
discharged, proving `ProjectionConstructionInput`.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace PlanarNikodym

namespace LocalTransverseProjectionData

/-- Construct the compact null/positive projection selection from
actual local analytic data. No finite-fan or refinement hypothesis
remains in this theorem. -/
theorem exists_compact_zero_positive_projection
    {φ ψ : ℝ × Plane → ℝ} {U V : Set (ℝ × Plane)}
    {t x : ℝ} {q : Plane}
    (B : LocalTransverseProjectionData φ ψ U V t x q) :
    ∃ G : Set Plane, IsCompact G ∧ MeasurableSet G ∧ G.Nonempty ∧
      G ⊆ B.parameterDomain ∧
      (∫⁻ a in B.curveTimes, volume ((fun z => φ (a, z)) '' G)) = 0 ∧
      0 < ∫⁻ a in B.centerTimes, volume ((fun z => ψ (a, z)) '' G) := by
  let ψσ : ℝ → Plane → ℝ := fun a z => B.sign * ψ (a, z)
  have hfan : ∀ W : Set Plane, IsOpen W → W ⊆ B.parameterDomain →
      ∀ (c : Plane) (l : ℝ), 0 < l →
        centeredBlindSegment c (-B.slopeMin, 1) l ⊆ W →
      ∀ e : ℝ, 0 < e →
        ∃ L : Set Plane, IsCompact L ∧ L ⊆ W ∧
          (∀ a ∈ B.centerTimes, ψσ a '' centeredBlindSegment c (-B.slopeMin, 1) l ⊆
            ψσ a '' interior L) ∧
          ∀ a ∈ B.curveTimes, volume ((fun z => φ (a, z)) '' L) ≤ ENNReal.ofReal e := by
    intro W hW hWU c l hl hseg e he
    let f : B.centerTimes → Plane → ℝ := fun a => ψσ a.val
    obtain ⟨L, hLc, hLW, hretain, hsmall⟩ :=
      exists_uniform_small_projection_segment_fan
        B.curveTimes_compact q B.radius_pos B.curve_analytic
        B.slope_lt.le B.headBound_pos he
        (fun p hp => ⟨B.curve_head p hp, B.curve_head_bound p hp⟩) B.curve_slope
        f B.derivativeLower_pos B.derivativeUpper_pos.le
        (fun a z hz => B.signedCenter_differentiableAt a.val a.property z hz)
        (fun a z hz => B.signedCenter_norm_le a.val a.property z hz)
        (fun s hs a z hz => B.signedCenter_direction_le a.val a.property z hz s hs)
        hW hWU c hl hseg
    exact ⟨L, hLc, hLW, fun a ha => hretain ⟨a, ha⟩, hsmall⟩
  obtain ⟨G, hGc, hGm, hGn, hGU, hG0, hGpos⟩ :=
    exists_compact_zero_positive_projection_of_local_fans
      (fun a z => φ (a, z)) ψσ
      B.curveTimes_measurable B.curveTimes_volume_lt_top
      B.centerTimes_open B.parameterDomain_open
      B.centerTimes_nonempty B.parameterDomain_nonempty
      B.curve_continuousOn B.signedCenter_continuousOn (-B.slopeMin, 1)
      B.signedCenter_differentiableAt B.signedCenter_fixed_direction_pos hfan
  refine ⟨G, hGc, hGm, hGn, hGU, hG0, ?_⟩
  have he :
      (∫⁻ a in B.centerTimes, volume (ψσ a '' G)) =
      ∫⁻ a in B.centerTimes, volume ((fun z => ψ (a, z)) '' G) :=
    lintegral_congr fun a => volume_signed_scalarProjection (fun z => ψ (a, z)) G B.sign_eq
  exact he ▸ hGpos

end LocalTransverseProjectionData

namespace ProjectionModel

/-- A constructed transverse patch of the actual two-slice gives the
Borel null set and positive-inner-measure centre trace in the original
scalar model. -/
theorem exists_null_set_of_twoSlice_localTransverseProjectionData
    {d : ℕ} (D : ProjectionModel d) {j : Fin (d + 1)}
    {t x : ℝ} {q : Plane}
    (B : LocalTransverseProjectionData (D.twoSliceCurves j) (D.twoSliceCenters j)
      (D.twoSliceCurveDomain j) (D.twoSliceCenterDomain j) t x q) :
    ∃ E : Set Plane, MeasurableSet E ∧ volume E = 0 ∧
      HasPositivePart volume (D.incidenceTrace E) := by
  obtain ⟨G, _hGc, hGm, _hGn, hGU, hG0, hGpos⟩ :=
    B.exists_compact_zero_positive_projection
  exact D.exists_null_set_of_twoSlice_projection_integrals j B.curveTimes B.centerTimes G
    B.curveTimes_measurable B.centerTimes_open.measurableSet hGm
    (B.twoSlice_curveTimes_subset.trans Ioo_subset_Icc_self) B.curveTimes_volume_pos
    B.twoSlice_centerTimes_subset
    (fun z hz => B.twoSlice_parameterDomain_subset (hGU hz)) hG0 hGpos

/-- Both scalar branches are actual constructions. In positive auxiliary
dimension the stationary branch uses Wisewell's construction; the other
branch uses the compact transverse projection selection. -/
theorem exists_null_set_positive_incidenceTrace
    {d : ℕ} (D : ProjectionModel d) (hd : 0 < d) :
    ∃ E : Set Plane, MeasurableSet E ∧ volume E = 0 ∧
      HasPositivePart volume (D.incidenceTrace E) := by
  rcases D.exists_null_set_or_twoSlice_localTransverseProjectionData hd with
    hE | ⟨j, t, x, q, _hj, ⟨B⟩⟩
  · exact hE
  · exact D.exists_null_set_of_twoSlice_localTransverseProjectionData B

end ProjectionModel

/-- The full scalar construction input, with its original quantifiers
and positive-inner-measure conclusion, is proved without any remaining
construction, selection, or analytic estimate hypothesis. -/
theorem projection_construction_input : ProjectionConstructionInput := by
  intro d hd D
  exact D.exists_null_set_positive_incidenceTrace hd

end PlanarNikodym
