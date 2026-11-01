import PlanarNikodym.Analysis.Maximal.E3SmoothNullPullback
import PlanarNikodym.Analysis.Maximal.E3InteriorIntervals
import PlanarNikodym.Analysis.Maximal.E3InteriorSmoothExtension
import Mathlib.MeasureTheory.Constructions.Pi

/-! The zero-auxiliary-dimensional cinematic exclusion follows from
the actual smooth time-jet Jacobian and Fubini. No local smoothing estimate
or analyticity hypothesis is used. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PlanarNikodym

theorem e3_parameterFrame_zero (v : Aux 2) :
    parameterFrame 0 v = (v, (0 : Aux 0)) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [parameterFrame]
  · exact Subsingleton.elim _ _

theorem Family.e3_cinematicJetMap_fderiv_invertible {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (t : ℝ) (v : Aux (d + 2)) (hd : G.cinematicDet (t, parameterFrame d v) ≠ 0) :
    (fderiv ℝ (G.cinematicJetMap t) v).IsInvertible := by
  apply isInvertible_of_det_coordinates
  have he : LinearMap.toMatrix' (fderiv ℝ (G.cinematicJetMap t) v).toLinearMap =
      G.cinematicMatrix (t, parameterFrame d v) := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    rw [G.cinematicMatrix_eq_jet_fderiv_smooth hG t v i j]
    exact (congrArg (fun L : Aux (d + 2) →L[ℝ] ℝ => L (Pi.single j 1))
      (fderiv_apply ((G.cinematicJetMap_contDiff hG t).differentiable
        (by simp)).differentiableAt i)).symm
  change (LinearMap.toMatrix' (fderiv ℝ (G.cinematicJetMap t) v).toLinearMap).det ≠ 0
  rw [he]
  exact hd

theorem e3_volume_coordinate_cylinder_null (A : Set ℝ) (hA : MeasurableSet A)
    (hA0 : volume A = 0) : volume {v : Aux 2 | v 0 ∈ A} = 0 := by
  have he : {v : Aux 2 | v 0 ∈ A} =
      (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹' (A ×ˢ (univ : Set ℝ)) := by
    ext v
    simp
  rw [he, (volume_preserving_finTwoArrow ℝ).measure_preimage
    (hA.prod MeasurableSet.univ).nullMeasurableSet]
  change (volume.prod volume) (A ×ˢ (univ : Set ℝ)) = 0
  rw [Measure.prod_prod, hA0, zero_mul]

/-- For a globally C∞ ambient phase, the d=0 branch of Corollary 1.2
is a direct change-of-variables and Fubini theorem. -/
theorem Family.e3_zero_dim_timeIncidence_null_of_contDiff (G : Family 2 0)
    (hW : IsOpen G.W)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 0 => G.γ x.1 x.2))
    (hd : ∀ t ∈ G.I.carrier, ∀ p ∈ G.W, G.cinematicDet (t, p) ≠ 0)
    (E : Set Plane) (hE : MeasurableSet E) (hE0 : volume E = 0) :
    volume (G.timeIncidenceCenters G.W E) = 0 := by
  have hsections : ∀ᵐ t : ℝ, volume (Prod.mk t ⁻¹' E) = 0 := by
    have h := hE0
    change (volume.prod volume) E = 0 at h
    rw [Measure.prod_apply hE] at h
    exact (lintegral_eq_zero_iff (measurable_measure_prodMk_left hE)).mp h
  let A : Set (ℝ × Aux 2) := {x | x.1 ∈ G.I.carrier ∧ (x.2, (0 : Aux 0)) ∈ G.W ∧
    (x.1, G.γ x.1 (x.2, 0)) ∈ E}
  have hA : MeasurableSet A := by
    exact (measurableSet_Icc.preimage measurable_fst).inter
      ((hW.measurableSet.preimage (by fun_prop)).inter
        (hE.preimage (continuous_fst.prodMk
          (hG.continuous.comp
            (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)))).measurable))
  have hfibers : ∀ᵐ t : ℝ, volume (Prod.mk t ⁻¹' A) = 0 := by
    filter_upwards [hsections] with t ht
    by_cases hti : t ∈ G.I.carrier
    · let B : Set (Aux 2) := {v | v 0 ∈ Prod.mk t ⁻¹' E}
      have hB : volume B = 0 := e3_volume_coordinate_cylinder_null _
        (hE.preimage (measurable_const.prodMk measurable_id)) ht
      have hregular := e3_smooth_regular_preimage_null (G.cinematicJetMap t)
        (G.cinematicJetMap_contDiff hG t) {v | (v, (0 : Aux 0)) ∈ G.W} volume B hB
      apply measure_mono_null (t := {v | (v, (0 : Aux 0)) ∈ G.W ∧
        (fderiv ℝ (G.cinematicJetMap t) v).IsInvertible ∧ G.cinematicJetMap t v ∈ B}) ?_ hregular
      intro v hv
      refine ⟨hv.2.1, G.e3_cinematicJetMap_fderiv_invertible hG t v ?_, ?_⟩
      · rw [e3_parameterFrame_zero]
        exact hd t hti (v, 0) hv.2.1
      · simpa only [B, mem_setOf_eq, Family.cinematicJetMap, Fin.val_zero,
          timeDerivative, e3_parameterFrame_zero, mem_preimage] using hv.2.2
    · have he : Prod.mk t ⁻¹' A = ∅ := by ext v; simp [A, hti]
      rw [he, measure_empty]
  have hA0 : (volume.prod volume) A = 0 := by
    rw [Measure.prod_apply hA]
    exact (lintegral_eq_zero_iff (measurable_measure_prodMk_left hA)).mpr hfibers
  rw [Measure.prod_apply_symm hA] at hA0
  have hbad := (lintegral_eq_zero_iff (measurable_measure_prodMk_right hA)).mp hA0
  apply measure_mono_null (t := {v : Aux 2 | volume ((fun t => (t, v)) ⁻¹' A) ≠ 0}) ?_
    (ae_iff.mp hbad)
  rintro z ⟨u, hu, hz⟩ hzero
  have hu0 : u = (0 : Aux 0) := Subsingleton.elim _ _
  subst u
  have he : (fun t => (t, z)) ⁻¹' A = G.hitTimes (z, 0) E := by
    ext t
    simp only [A, mem_preimage, mem_setOf_eq, hu, true_and,
      Family.hitTimes, Family.graphMap]
  exact hz.ne' (he ▸ hzero)

/-- The original closed-interval, generally C∞ d=0 hypothesis suffices.
Every extension used in the proof is explicitly constructed on a compact
interior interval, and the two original endpoints are discarded as null. -/
theorem Family.e3_zero_dim_timeIncidence_null_of_isSmooth (G : Family 2 0)
    (hW : IsOpen G.W) (hG : G.IsSmooth)
    (hd : ∀ t ∈ G.I.carrier, ∀ p ∈ G.W, G.cinematicDet (t, p) ≠ 0)
    (E : Set Plane) (hE : MeasurableSet E) (hE0 : volume E = 0) :
    volume (G.timeIncidenceCenters G.W E) = 0 := by
  apply G.timeIncidenceCenters_null_of_interiorIntervals G.W E
  intro i
  let J := interiorInterval G.I i
  have hJ : J.carrier ⊆ G.I.carrier :=
    (interiorInterval_subset G.I i).trans Ioo_subset_Icc_self
  have hGs : (G.withInterval J).IsSmooth := hG.mono (prod_mono hJ Subset.rfl)
  rw [(G.withInterval J).timeIncidenceCenters_eq hGs G.W Subset.rfl E]
  apply (G.withInterval J).incidence_null_of_local ?_ E hE hE0
  intro q hq
  obtain ⟨U, H, hU, hqU, hUW, hI, hHW, hH, heq, hdet⟩ :=
    G.exists_e3_interior_smooth_extension hW hG i q hq
  refine ⟨U, hU, hqU, ?_⟩
  intro F hF hF0
  have hHd : ∀ t ∈ H.I.carrier, ∀ p ∈ H.W, H.cinematicDet (t, p) ≠ 0 := by
    intro t ht p hp
    have htJ : t ∈ J.carrier := by simpa only [hI] using ht
    have hpU : p ∈ U := hHW ▸ hp
    rw [hdet (t, p) ⟨htJ, hpU⟩]
    exact hd t (hJ htJ) p (hUW hpU)
  have hnullH := H.e3_zero_dim_timeIncidence_null_of_contDiff (hHW.symm ▸ hU)
    hH hHd F hF hF0
  rw [H.timeIncidenceCenters_eq hH.contDiffOn H.W Subset.rfl F] at hnullH
  apply measure_mono_null (t := H.incidenceCenters H.W F) ?_ hnullH
  rintro z ⟨u, hu, hz⟩
  refine ⟨u, hHW.symm ▸ hu, ?_⟩
  have hcurve : (G.withInterval J).curve (z, u) = H.curve (z, u) := by
    change (fun t => (t, G.γ t (z, u))) '' J.carrier =
      (fun t => (t, H.γ t (z, u))) '' H.I.carrier
    rw [hI]
    apply Set.image_congr
    intro t ht
    exact Prod.ext rfl (heq t ht (z, u) hu).symm
  rwa [← hcurve]

/-- Corollary 1.2 in auxiliary dimension zero, with precisely the original
smooth closed-interval hypothesis and the actual cinematic determinant. -/
theorem corollary_1_2_zero_dim_smooth (G : Family 2 0)
    (hW : IsOpen G.W) (hG : G.IsSmooth)
    (hd : ∀ t ∈ G.I.carrier, ∀ p ∈ G.W, G.cinematicDet (t, p) ≠ 0) :
    ¬ G.AdmitsNikodym := by
  apply G.no_nikodym_of_incidence_null
  intro E hE hE0
  rw [← G.timeIncidenceCenters_eq hG G.W Subset.rfl E]
  exact G.e3_zero_dim_timeIncidence_null_of_isSmooth hW hG hd E hE hE0

end PlanarNikodym
