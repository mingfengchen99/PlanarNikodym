import PlanarNikodym.Geometry.AnalyticImplicit
import Mathlib.Topology.Order.IntermediateValue

/-! Actual coordinates on the open band between two ordered graphs.
The map fixes every retained parameter and rescales only the last real
coordinate. Both directions are analytic on their actual domains. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

variable {E : Type*}

def analyticBand (U : Set E) (l u : E → ℝ) : Set (E × ℝ) :=
  {z | z.1 ∈ U ∧ l z.1 < z.2 ∧ z.2 < u z.1}

def analyticBandMap (l u : E → ℝ) (z : E × ℝ) : E × ℝ :=
  (z.1, l z.1 + z.2 * (u z.1 - l z.1))

def analyticBandInverse (l u : E → ℝ) (z : E × ℝ) : E × ℝ :=
  (z.1, (z.2 - l z.1) / (u z.1 - l z.1))

@[simp] theorem analyticBandMap_fst (l u : E → ℝ) (z : E × ℝ) :
    (analyticBandMap l u z).1 = z.1 := rfl

@[simp] theorem analyticBandInverse_fst (l u : E → ℝ) (z : E × ℝ) :
    (analyticBandInverse l u z).1 = z.1 := rfl

theorem analyticBandMap_mapsTo {U : Set E} (l u : E → ℝ)
    (hlt : ∀ x ∈ U, l x < u x) :
    MapsTo (analyticBandMap l u) (U ×ˢ Ioo (0 : ℝ) 1) (analyticBand U l u) := by
  intro z hz
  have hd : 0 < u z.1 - l z.1 := sub_pos.mpr (hlt z.1 hz.1)
  refine ⟨hz.1, ?_, ?_⟩
  · change l z.1 < l z.1 + z.2 * (u z.1 - l z.1)
    exact lt_add_of_pos_right _ (mul_pos hz.2.1 hd)
  · change l z.1 + z.2 * (u z.1 - l z.1) < u z.1
    nlinarith [mul_lt_mul_of_pos_right hz.2.2 hd]

theorem analyticBandInverse_mapsTo {U : Set E} (l u : E → ℝ) :
    MapsTo (analyticBandInverse l u) (analyticBand U l u) (U ×ˢ Ioo (0 : ℝ) 1) := by
  intro z hz
  have hd : 0 < u z.1 - l z.1 := by linarith [hz.2.1, hz.2.2]
  refine ⟨hz.1, ?_, ?_⟩
  · exact div_pos (sub_pos.mpr hz.2.1) hd
  · exact (div_lt_one hd).mpr (by linarith [hz.2.2])

theorem analyticBand_left_inv {U : Set E} (l u : E → ℝ)
    (hlt : ∀ x ∈ U, l x < u x) {z : E × ℝ} (hz : z.1 ∈ U) :
    analyticBandInverse l u (analyticBandMap l u z) = z := by
  have hd := (sub_pos.mpr (hlt z.1 hz)).ne'
  apply Prod.ext
  · rfl
  · dsimp [analyticBandInverse, analyticBandMap]
    field_simp
    ring

theorem analyticBand_right_inv {U : Set E} (l u : E → ℝ)
    (hlt : ∀ x ∈ U, l x < u x) {z : E × ℝ} (hz : z.1 ∈ U) :
    analyticBandMap l u (analyticBandInverse l u z) = z := by
  have hd := (sub_pos.mpr (hlt z.1 hz)).ne'
  apply Prod.ext
  · rfl
  · dsimp [analyticBandInverse, analyticBandMap]
    field_simp
    ring

theorem analyticBandMap_image {U : Set E} (l u : E → ℝ)
    (hlt : ∀ x ∈ U, l x < u x) :
    analyticBandMap l u '' (U ×ˢ Ioo (0 : ℝ) 1) = analyticBand U l u := by
  apply Subset.antisymm
  · exact (analyticBandMap_mapsTo l u hlt).image_subset
  · intro z hz
    exact ⟨analyticBandInverse l u z, analyticBandInverse_mapsTo l u hz,
      analyticBand_right_inv l u hlt hz.1⟩

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analyticAt_analyticBandMap {l u : E → ℝ} {z : E × ℝ}
    (hl : AnalyticAt ℝ l z.1) (hu : AnalyticAt ℝ u z.1) :
    AnalyticAt ℝ (analyticBandMap l u) z :=
  analyticAt_fst.prod ((hl.comp analyticAt_fst).add
    (analyticAt_snd.mul ((hu.comp analyticAt_fst).sub (hl.comp analyticAt_fst))))

theorem analyticAt_analyticBandInverse {l u : E → ℝ} {z : E × ℝ}
    (hl : AnalyticAt ℝ l z.1) (hu : AnalyticAt ℝ u z.1) (hlt : l z.1 < u z.1) :
    AnalyticAt ℝ (analyticBandInverse l u) z :=
  analyticAt_fst.prod ((analyticAt_snd.sub (hl.comp analyticAt_fst)).div
    ((hu.comp analyticAt_fst).sub (hl.comp analyticAt_fst)) (sub_pos.mpr hlt).ne')

theorem analyticOnNhd_analyticBandMap {U : Set E} {l u : E → ℝ}
    (hl : AnalyticOnNhd ℝ l U) (hu : AnalyticOnNhd ℝ u U) :
    AnalyticOnNhd ℝ (analyticBandMap l u) (U ×ˢ Ioo (0 : ℝ) 1) :=
  fun z hz => analyticAt_analyticBandMap (hl z.1 hz.1) (hu z.1 hz.1)

theorem analyticOnNhd_analyticBandInverse {U : Set E} {l u : E → ℝ}
    (hl : AnalyticOnNhd ℝ l U) (hu : AnalyticOnNhd ℝ u U) :
    AnalyticOnNhd ℝ (analyticBandInverse l u) (analyticBand U l u) :=
  fun z hz => analyticAt_analyticBandInverse (hl z.1 hz.1) (hu z.1 hz.1)
    (hz.2.1.trans hz.2.2)

theorem isOpen_analyticBand {U : Set E} {l u : E → ℝ}
    (hU : IsOpen U) (hl : AnalyticOnNhd ℝ l U) (hu : AnalyticOnNhd ℝ u U) :
    IsOpen (analyticBand U l u) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hUl : {w : E × ℝ | w.1 ∈ U} ∈ 𝓝 z :=
    continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hz.1)
  have hlz := (hl z.1 hz.1).continuousAt.comp continuous_fst.continuousAt
  have huz := (hu z.1 hz.1).continuousAt.comp continuous_fst.continuousAt
  filter_upwards [hUl, hlz.eventually_lt continuous_snd.continuousAt hz.2.1,
    continuous_snd.continuousAt.eventually_lt huz hz.2.2] with w hw hwl hwu
  exact ⟨hw, hwl, hwu⟩

/-- The actual coordinate map is a homeomorphism of the two subspaces. -/
def analyticBandHomeomorph {U : Set E} (l u : E → ℝ)
    (hl : AnalyticOnNhd ℝ l U) (hu : AnalyticOnNhd ℝ u U)
    (hlt : ∀ x ∈ U, l x < u x) :
    (U ×ˢ Ioo (0 : ℝ) 1) ≃ₜ analyticBand U l u where
  toFun z := ⟨analyticBandMap l u z, analyticBandMap_mapsTo l u hlt z.2⟩
  invFun z := ⟨analyticBandInverse l u z, analyticBandInverse_mapsTo l u z.2⟩
  left_inv z := Subtype.ext (analyticBand_left_inv l u hlt z.2.1)
  right_inv z := Subtype.ext (analyticBand_right_inv l u hlt z.2.1)
  continuous_toFun :=
    (analyticOnNhd_analyticBandMap hl hu).continuousOn.restrict.subtype_mk _
  continuous_invFun :=
    (analyticOnNhd_analyticBandInverse hl hu).continuousOn.restrict.subtype_mk _

/-- Connected retained parameters give a connected band, even when the
boundary graphs are not affine and the band is not convex. -/
theorem isConnected_analyticBand {U : Set E} {l u : E → ℝ}
    (hU : IsConnected U) (hl : AnalyticOnNhd ℝ l U) (hu : AnalyticOnNhd ℝ u U)
    (hlt : ∀ x ∈ U, l x < u x) : IsConnected (analyticBand U l u) := by
  rw [← analyticBandMap_image l u hlt]
  exact (hU.prod (isConnected_Ioo (by norm_num : (0 : ℝ) < 1))).image
    (analyticBandMap l u) (analyticOnNhd_analyticBandMap hl hu).continuousOn

end PlanarNikodym
