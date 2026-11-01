import PlanarNikodym.Geometry.AnalyticStratificationCharts
import Mathlib.Topology.Bornology.Constructions

/-! Explicit one-dimension-higher analytic band strata above an actual
parametrized base stratum. The source is an open bounded connected subset
of `Fin (dim + 1) → ℝ`, with an explicit inverse on the band image. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym
namespace AnalyticStratificationChart
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def unitProduct (Q : AnalyticStratificationChart E) : AnalyticStratificationChart (E × ℝ) := by
  let e := realCoordinateSplitEquiv (Fin.last Q.dim)
  let V := Q.source ×ˢ Ioo (0 : ℝ) 1
  let W := e.symm ⁻¹' V
  let F : (Fin (Q.dim + 1) → ℝ) → E × ℝ :=
    fun p => (Q.map (e.symm p).1, (e.symm p).2)
  let I : E × ℝ → (Fin (Q.dim + 1) → ℝ) := fun z => e (Q.inverse z.1, z.2)
  have hWimage : W = e '' V := (e.toHomeomorph.image_eq_preimage_symm V).symm
  have hFimage : F '' W = Q.image ×ˢ Ioo (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨mem_image_of_mem _ hp.1, hp.2⟩
    · rintro ⟨⟨p, hp, hmap⟩, ht⟩
      refine ⟨e (p, z.2), ?_, ?_⟩
      · change e.symm (e (p, z.2)) ∈ V
        rw [e.symm_apply_apply]
        exact ⟨hp, ht⟩
      · change (Q.map (e.symm (e (p, z.2))).1, (e.symm (e (p, z.2))).2) = z
        rw [e.symm_apply_apply]
        exact Prod.ext hmap rfl
  refine { dim := Q.dim + 1
           source := W
           open_source := (Q.open_source.prod isOpen_Ioo).preimage e.symm.continuous
           bounded_source := ?_
           connected_source := ?_
           map := F
           inverse := I
           analytic_map := ?_
           continuous_inverse := ?_
           left_inverse := ?_
           derivative_injective := ?_ }
  · rw [hWimage]
    exact e.toContinuousLinearMap.lipschitz.isBounded_image
      (Q.bounded_source.prod (Metric.isBounded_Ioo 0 1))
  · rw [hWimage]
    exact (Q.connected_source.prod (isConnected_Ioo (by norm_num : (0 : ℝ) < 1))).image
      e e.continuous.continuousOn
  · intro p hp
    have he := e.symm.analyticAt p
    have hf : AnalyticAt ℝ (fun z => (e.symm z).1) p :=
      AnalyticAt.comp (f := fun z => e.symm z) (g := Prod.fst) analyticAt_fst he
    have hs : AnalyticAt ℝ (fun z => (e.symm z).2) p :=
      AnalyticAt.comp (f := fun z => e.symm z) (g := Prod.snd) analyticAt_snd he
    have hfirst : AnalyticAt ℝ (fun z => Q.map (e.symm z).1) p :=
      AnalyticAt.comp (f := fun z => (e.symm z).1) (g := Q.map) (Q.analytic_map _ hp.1) hf
    exact hfirst.prod hs
  · have hmaps : MapsTo Prod.fst (F '' W) Q.image := by
      rw [hFimage]
      exact fun _ hz => hz.1
    have hbase := Q.continuous_inverse.comp continuous_fst.continuousOn hmaps
    exact e.continuous.comp_continuousOn (hbase.prodMk continuous_snd.continuousOn)
  · intro p hp
    change e (Q.inverse (Q.map (e.symm p).1), (e.symm p).2) = p
    rw [Q.left_inverse _ hp.1]
    exact e.apply_symm_apply p
  · intro p hp
    let L := (fderiv ℝ Q.map (e.symm p).1).prodMap (ContinuousLinearMap.id ℝ ℝ)
    have hL : Function.Injective L := by
      intro v w hvw
      apply Prod.ext
      · exact Q.derivative_injective _ hp.1 (congrArg Prod.fst hvw)
      · have hh := congrArg Prod.snd hvw
        exact hh
    have hprod : HasFDerivAt (Prod.map Q.map (id : ℝ → ℝ)) L (e.symm p) :=
      HasFDerivAt.prodMap (p := e.symm p)
        (Q.analytic_map _ hp.1).differentiableAt.hasFDerivAt
        (hasFDerivAt_id (𝕜 := ℝ) (e.symm p).2)
    have hd : HasFDerivAt F (L.comp e.symm.toContinuousLinearMap) p :=
      hprod.comp p e.symm.toContinuousLinearMap.hasFDerivAt
    rw [hd.fderiv]
    exact hL.comp e.symm.injective

@[simp] theorem unitProduct_dim (Q : AnalyticStratificationChart E) :
    Q.unitProduct.dim = Q.dim + 1 := rfl

@[simp] theorem unitProduct_image (Q : AnalyticStratificationChart E) :
    Q.unitProduct.image = Q.image ×ˢ Ioo (0 : ℝ) 1 := by
  let e := realCoordinateSplitEquiv (Fin.last Q.dim)
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨mem_image_of_mem _ hp.1, hp.2⟩
  · rintro ⟨⟨p, hp, hmap⟩, ht⟩
    refine ⟨e (p, z.2), ?_, ?_⟩
    · change e.symm (e (p, z.2)) ∈ Q.source ×ˢ Ioo (0 : ℝ) 1
      rw [e.symm_apply_apply]
      exact ⟨hp, ht⟩
    · change (Q.map (e.symm (e (p, z.2))).1, (e.symm (e (p, z.2))).2) = z
      rw [e.symm_apply_apply]
      exact Prod.ext hmap rfl

def band (Q : AnalyticStratificationChart E) (l u : E → ℝ)
    (hl : AnalyticOnNhd ℝ l Q.image) (hu : AnalyticOnNhd ℝ u Q.image)
    (hlt : ∀ x ∈ Q.image, l x < u x) : AnalyticStratificationChart (E × ℝ) := by
  have hmap : analyticBandMap l u '' Q.unitProduct.image = analyticBand Q.image l u := by
    rw [unitProduct_image]
    exact analyticBandMap_image l u hlt
  apply Q.unitProduct.postcompose (analyticBandMap l u) (analyticBandInverse l u)
  · rw [unitProduct_image]
    exact analyticOnNhd_analyticBandMap hl hu
  · rw [hmap]
    exact analyticOnNhd_analyticBandInverse hl hu
  · intro z hz
    rw [unitProduct_image] at hz
    exact analyticBand_left_inv l u hlt hz.1

@[simp] theorem band_dim (Q : AnalyticStratificationChart E) (l u : E → ℝ)
    (hl : AnalyticOnNhd ℝ l Q.image) (hu : AnalyticOnNhd ℝ u Q.image)
    (hlt : ∀ x ∈ Q.image, l x < u x) : (Q.band l u hl hu hlt).dim = Q.dim + 1 := rfl

@[simp] theorem band_image (Q : AnalyticStratificationChart E) (l u : E → ℝ)
    (hl : AnalyticOnNhd ℝ l Q.image) (hu : AnalyticOnNhd ℝ u Q.image)
    (hlt : ∀ x ∈ Q.image, l x < u x) :
    (Q.band l u hl hu hlt).image = analyticBand Q.image l u := by
  rw [band, postcompose_image, unitProduct_image]
  exact analyticBandMap_image l u hlt

end AnalyticStratificationChart
end PlanarNikodym
