import PlanarNikodym.Analysis.Sobolev.ScaledSobolevTwo
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! The two-dimensional tensor estimate in actual `Aux 2` coordinates,
using full Fréchet jets and integrated over the base variables. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal

namespace PlanarNikodym

def auxTwoPlaneEquiv : Aux 2 ≃ₗᵢ[ℝ] Plane :=
  { LinearEquiv.finTwoArrow ℝ ℝ with
    norm_map' := by
      intro u
      simp [LinearEquiv.finTwoArrow, Pi.norm_def, Prod.norm_def, Finset.univ_fin2] }

theorem auxTwoPlaneEquiv_measurePreserving :
    MeasurePreserving auxTwoPlaneEquiv volume volume := volume_preserving_finTwoArrow ℝ

theorem norm_partialFirst_le_fderiv {F : Plane → ℂ} {q : Plane}
    (hF : DifferentiableAt ℝ F q) : ‖partialFirst F q‖ ≤ ‖fderiv ℝ F q‖ := by
  rw [partialFirst_eq_fderiv hF]
  exact (fderiv ℝ F q).unit_le_opNorm (1, 0) (by simp)

theorem norm_partialSecond_le_fderiv {F : Plane → ℂ} {q : Plane}
    (hF : DifferentiableAt ℝ F q) : ‖partialSecond F q‖ ≤ ‖fderiv ℝ F q‖ := by
  rw [partialSecond_eq_fderiv hF]
  exact (fderiv ℝ F q).unit_le_opNorm (0, 1) (by simp)

theorem norm_mixed_partial_le_iteratedFDeriv_two {F : Plane → ℂ}
    (hF : ContDiff ℝ 2 F) (q : Plane) :
    ‖partialSecond (partialFirst F) q‖ ≤ ‖iteratedFDeriv ℝ 2 F q‖ := by
  have hFone : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hFD : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have heq : partialFirst F = fun q => fderiv ℝ F q (1, 0) :=
    funext (fun q => partialFirst_eq_fderiv (hFone.differentiable one_ne_zero q))
  have hFirst : ContDiff ℝ 1 (partialFirst F) := by
    rw [heq]
    exact hFD.clm_apply contDiff_const
  have hbound := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ F)
    (c := ((1, 0) : Plane)) (x := q) (n := 1) hFD.contDiffAt (by norm_num)
  simp only [norm_iteratedFDeriv_one, Prod.norm_def, norm_one, norm_zero,
    max_eq_left zero_le_one, one_mul] at hbound
  have hnorm : ‖fderiv ℝ (fderiv ℝ F) q‖ = ‖iteratedFDeriv ℝ 2 F q‖ := by
    simpa only [norm_iteratedFDeriv_one] using
      (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (x := q) (n := 1))
  calc
    _ ≤ ‖fderiv ℝ (partialFirst F) q‖ :=
      norm_partialSecond_le_fderiv (hFirst.differentiable one_ne_zero q)
    _ ≤ ‖fderiv ℝ (fderiv ℝ F) q‖ := by simpa only [heq] using hbound
    _ = _ := hnorm

/-- Full Fréchet derivatives control the coordinate derivatives in the
two-dimensional tensor Sobolev estimate. -/
theorem iSup_enorm_le_scaled_fullJet_two {F : Plane → ℂ}
    (hF : ContDiff ℝ 2 F) (p : ℝ≥0) (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) :
    (⨆ q : Plane, ‖F q‖ₑ) ≤ 2 * ENNReal.ofReal r ^ (-2 / (p : ℝ)) *
      (eLpNorm F p volume + ENNReal.ofReal r * eLpNorm (fderiv ℝ F) p volume +
        ENNReal.ofReal r ^ 2 * eLpNorm (iteratedFDeriv ℝ 2 F) p volume) := by
  have hFone : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have h₁ : eLpNorm (partialFirst F) p volume ≤ eLpNorm (fderiv ℝ F) p volume :=
    eLpNorm_mono (fun q => norm_partialFirst_le_fderiv (hFone.differentiable one_ne_zero q))
  have h₂ : eLpNorm (partialSecond F) p volume ≤ eLpNorm (fderiv ℝ F) p volume :=
    eLpNorm_mono (fun q => norm_partialSecond_le_fderiv (hFone.differentiable one_ne_zero q))
  have h₂₁ : eLpNorm (partialSecond (partialFirst F)) p volume ≤
      eLpNorm (iteratedFDeriv ℝ 2 F) p volume :=
    eLpNorm_mono (norm_mixed_partial_le_iteratedFDeriv_two hF)
  have hdouble (N : ℝ≥0∞) : N ≤ 2 * N := by
    simpa [mul_comm] using mul_le_mul_right (show (1 : ℝ≥0∞) ≤ 2 by norm_num) N
  calc
    _ ≤ _ := iSup_enorm_le_scaled_eLpNorm_two_of_contDiff hF p hp hr
    _ ≤ ENNReal.ofReal r ^ (-2 / (p : ℝ)) *
        (eLpNorm F p volume + ENNReal.ofReal r * eLpNorm (fderiv ℝ F) p volume +
          ENNReal.ofReal r * eLpNorm (fderiv ℝ F) p volume +
          ENNReal.ofReal r ^ 2 * eLpNorm (iteratedFDeriv ℝ 2 F) p volume) := by gcongr
    _ ≤ ENNReal.ofReal r ^ (-2 / (p : ℝ)) *
        (2 * eLpNorm F p volume + ENNReal.ofReal r * eLpNorm (fderiv ℝ F) p volume +
          ENNReal.ofReal r * eLpNorm (fderiv ℝ F) p volume +
          2 * (ENNReal.ofReal r ^ 2 * eLpNorm (iteratedFDeriv ℝ 2 F) p volume)) := by
      exact mul_le_mul_right
        (add_le_add (add_le_add (add_le_add (hdouble _) le_rfl) le_rfl) (hdouble _)) _
    _ = _ := by ring

/-- The full-jet estimate transported through the actual volume-preserving
linear isometry `Aux 2 ≃ ℝ × ℝ`. -/
theorem iSup_enorm_aux_two_le_scaled_fullJet {F : Aux 2 → ℂ}
    (hF : ContDiff ℝ 2 F) (p : ℝ≥0) (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) :
    (⨆ u : Aux 2, ‖F u‖ₑ) ≤ 2 * ENNReal.ofReal r ^ (-2 / (p : ℝ)) *
      (eLpNorm F p volume + ENNReal.ofReal r *
          eLpNorm (fun u => ‖iteratedFDeriv ℝ 1 F u‖) p volume +
        ENNReal.ofReal r ^ 2 * eLpNorm (fun u => ‖iteratedFDeriv ℝ 2 F u‖) p volume) := by
  let e := auxTwoPlaneEquiv.symm
  have he : MeasurePreserving e volume volume :=
    (volume_preserving_finTwoArrow ℝ).symm _
  have hFC : ContDiff ℝ 2 (F ∘ e) := hF.comp e.contDiff
  have hj (j : ℕ) (hj : j ≤ 2) :
      eLpNorm (fun q : Plane => ‖iteratedFDeriv ℝ j (F ∘ e) q‖) p volume =
        eLpNorm (fun u : Aux 2 => ‖iteratedFDeriv ℝ j F u‖) p volume := by
    have hfun : (fun q : Plane => ‖iteratedFDeriv ℝ j (F ∘ e) q‖) =
        (fun u : Aux 2 => ‖iteratedFDeriv ℝ j F u‖) ∘ e := by
      funext q
      exact e.norm_iteratedFDeriv_comp_right F q j
    rw [hfun]
    exact eLpNorm_comp_measurePreserving
      (hF.continuous_iteratedFDeriv (by exact_mod_cast hj)).norm.aestronglyMeasurable he
  have h₀ : eLpNorm (F ∘ e) p volume = eLpNorm F p volume :=
    eLpNorm_comp_measurePreserving hF.continuous.aestronglyMeasurable he
  have h₁ : eLpNorm (fderiv ℝ (F ∘ e)) p volume =
      eLpNorm (fun u : Aux 2 => ‖iteratedFDeriv ℝ 1 F u‖) p volume := by
    rw [← eLpNorm_norm]
    simpa only [norm_iteratedFDeriv_one] using hj 1 (by norm_num)
  have h₂ : eLpNorm (iteratedFDeriv ℝ 2 (F ∘ e)) p volume =
      eLpNorm (fun u : Aux 2 => ‖iteratedFDeriv ℝ 2 F u‖) p volume := by
    rw [← eLpNorm_norm]
    exact hj 2 le_rfl
  have h := iSup_enorm_le_scaled_fullJet_two hFC p hp hr
  rw [h₀, h₁, h₂] at h
  simp only [Function.comp_apply] at h
  rw [show (⨆ q : Plane, ‖F (e q)‖ₑ) = ⨆ u : Aux 2, ‖F u‖ₑ from
    e.surjective.iSup_comp (fun u => ‖F u‖ₑ)] at h
  exact h

section RealFiberNorm
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]

theorem measurable_real_fiber_eLpNorm {F : X × Y → ℝ} (hF : Measurable F)
    (p : ℝ≥0) (hp : p ≠ 0) :
    Measurable (fun x => eLpNorm (fun y => F (x, y)) p ν) := by
  simp_rw [eLpNorm_nnreal_eq_lintegral hp]
  exact ((hF.enorm.pow_const (p : ℝ)).lintegral_prod_right').pow_const _

theorem eLpNorm_real_fiber_eLpNorm {F : X × Y → ℝ} (hF : Measurable F)
    (p : ℝ≥0) (hp : p ≠ 0) :
    eLpNorm (fun x => eLpNorm (fun y => F (x, y)) p ν) p μ =
      eLpNorm F p (μ.prod ν) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  simp_rw [eLpNorm_nnreal_eq_lintegral hp, enorm_eq_self,
    ← ENNReal.rpow_mul, one_div_mul_cancel hpR, ENNReal.rpow_one]
  rw [← lintegral_prod _ (hF.enorm.pow_const (p : ℝ)).aemeasurable]

end RealFiberNorm

/-- The actual two-auxiliary-variable full-jet Sobolev estimate, integrated
over an arbitrary base measure. -/
theorem eLpNorm_iSup_aux_two_le_scaled_fullJet
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {H : X × Aux 2 → ℂ} (hH : Measurable H)
    (hJ₁ : Measurable (fun q : X × Aux 2 =>
      ‖iteratedFDeriv ℝ 1 (fun u => H (q.1, u)) q.2‖))
    (hJ₂ : Measurable (fun q : X × Aux 2 =>
      ‖iteratedFDeriv ℝ 2 (fun u => H (q.1, u)) q.2‖))
    (hC : ∀ x, ContDiff ℝ 2 (fun u => H (x, u)))
    (p : ℝ≥0) (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x => ⨆ u : Aux 2, ‖H (x, u)‖ₑ) p μ ≤
      2 * ENNReal.ofReal r ^ (-2 / (p : ℝ)) *
        (eLpNorm H p (μ.prod volume) + ENNReal.ofReal r *
          eLpNorm (fun q : X × Aux 2 =>
            ‖iteratedFDeriv ℝ 1 (fun u => H (q.1, u)) q.2‖) p (μ.prod volume) +
          ENNReal.ofReal r ^ 2 * eLpNorm (fun q : X × Aux 2 =>
            ‖iteratedFDeriv ℝ 2 (fun u => H (q.1, u)) q.2‖) p (μ.prod volume)) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  let J₁ : X × Aux 2 → ℝ := fun q => ‖iteratedFDeriv ℝ 1 (fun u => H (q.1, u)) q.2‖
  let J₂ : X × Aux 2 → ℝ := fun q => ‖iteratedFDeriv ℝ 2 (fun u => H (q.1, u)) q.2‖
  let N₀ : X → ℝ≥0∞ := fun x => eLpNorm (fun u => H (x, u)) p volume
  let N₁ : X → ℝ≥0∞ := fun x => eLpNorm (fun u => J₁ (x, u)) p volume
  let N₂ : X → ℝ≥0∞ := fun x => eLpNorm (fun u => J₂ (x, u)) p volume
  let R : ℝ≥0∞ := ENNReal.ofReal r
  let A : ℝ≥0∞ := 2 * R ^ (-2 / (p : ℝ))
  have hN₀ : Measurable N₀ := measurable_fiber_eLpNorm volume hH p hp0
  have hN₁ : Measurable N₁ := measurable_real_fiber_eLpNorm volume hJ₁ p hp0
  have hN₂ : Measurable N₂ := measurable_real_fiber_eLpNorm volume hJ₂ p hp0
  have hB : Measurable (fun x => N₀ x + R * N₁ x) := hN₀.add (measurable_const.mul hN₁)
  have hD : Measurable (fun x => R ^ 2 * N₂ x) := measurable_const.mul hN₂
  have hm (x : X) : (⨆ u : Aux 2, ‖H (x, u)‖ₑ) ≤
      A * (N₀ x + R * N₁ x + R ^ 2 * N₂ x) :=
    iSup_enorm_aux_two_le_scaled_fullJet (hC x) p hp hr
  calc
    _ ≤ eLpNorm (fun x => A * (N₀ x + R * N₁ x + R ^ 2 * N₂ x)) p μ :=
      eLpNorm_mono_enorm (by simpa only [enorm_eq_self] using hm)
    _ = A * eLpNorm (fun x => N₀ x + R * N₁ x + R ^ 2 * N₂ x) p μ :=
      eLpNorm_ennreal_const_mul μ (hB.add hD) p hp0 A
    _ ≤ A * (eLpNorm (fun x => N₀ x + R * N₁ x) p μ +
        eLpNorm (fun x => R ^ 2 * N₂ x) p μ) := by
      gcongr
      exact eLpNorm_add_le hB.stronglyMeasurable.aestronglyMeasurable
        hD.stronglyMeasurable.aestronglyMeasurable (by exact_mod_cast hp)
    _ ≤ A * ((eLpNorm N₀ p μ + eLpNorm (fun x => R * N₁ x) p μ) +
        eLpNorm (fun x => R ^ 2 * N₂ x) p μ) := by
      gcongr
      exact eLpNorm_add_le hN₀.stronglyMeasurable.aestronglyMeasurable
        (measurable_const.mul hN₁).stronglyMeasurable.aestronglyMeasurable
        (by exact_mod_cast hp)
    _ = _ := by
      rw [eLpNorm_ennreal_const_mul μ hN₁ p hp0,
        eLpNorm_ennreal_const_mul μ hN₂ p hp0]
      rw [eLpNorm_fiber_eLpNorm μ volume hH p hp0,
        eLpNorm_real_fiber_eLpNorm μ volume hJ₁ p hp0,
        eLpNorm_real_fiber_eLpNorm μ volume hJ₂ p hp0]

/-- The actual first auxiliary derivative is jointly `C¹` for a jointly
`C²` function, in every finite parameter dimension. -/
theorem contDiff_one_auxiliary_fderiv_of_contDiff_two {n d : ℕ}
    {H : Parameters n d → ℂ} (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 1 (fun q : Parameters n d => fderiv ℝ (fun u => H (q.1, u)) q.2) := by
  have hdup : ContDiff ℝ 2 (Function.uncurry
      (fun q : Parameters n d => fun u : Aux d => H (q.1, u))) :=
    hH.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hdup.fderiv contDiff_snd (by norm_num)

/-- The norm of the actual second auxiliary jet is jointly continuous for a
jointly `C²` function. -/
theorem continuous_auxiliaryJet_two_of_contDiff_two {n d : ℕ}
    {H : Parameters n d → ℂ} (hH : ContDiff ℝ 2 H) :
    Continuous (fun q : Parameters n d =>
      ‖iteratedFDeriv ℝ 2 (fun u => H (q.1, u)) q.2‖) := by
  let D : Parameters n d → Aux d →L[ℝ] ℂ := fun q => fderiv ℝ (fun u => H (q.1, u)) q.2
  have hD : ContDiff ℝ 1 D := contDiff_one_auxiliary_fderiv_of_contDiff_two hH
  have hdup : ContDiff ℝ 1 (Function.uncurry
      (fun q : Parameters n d => fun u : Aux d => D (q.1, u))) :=
    hD.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hDD : Continuous (fun q : Parameters n d => fderiv ℝ (fun u => D (q.1, u)) q.2) :=
    Continuous.fderiv_one hdup continuous_snd
  have heq : (fun q : Parameters n d => ‖iteratedFDeriv ℝ 2 (fun u => H (q.1, u)) q.2‖) =
      fun q => ‖fderiv ℝ (fun u => D (q.1, u)) q.2‖ := by
    funext q
    symm
    simpa only [norm_iteratedFDeriv_one, D] using
      (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun u => H (q.1, u)) (x := q.2) (n := 1))
  rw [heq]
  have hn : Continuous (fun L : Aux d →L[ℝ] Aux d →L[ℝ] ℂ => ‖L‖) :=
    @continuous_norm _ (ContinuousLinearMap.toSeminormedAddCommGroup
      (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Aux d) (F := Aux d →L[ℝ] ℂ)
      (σ₁₂ := RingHom.id ℝ)).toSeminormedAddGroup
  exact hn.comp hDD

/-- The actual two-parameter maximal average is controlled by its finite
full jet with the correct dyadic scale exponent. -/
theorem Family.cutoffMaximal_le_scaledJetNorm_aux_two_of_contDiff
    (G : Family 2 2) (χ : Cutoff 2) (f : Plane → ℂ)
    (hH : ContDiff ℝ 2 (G.cutoffAverage χ f)) (p : ℝ≥0) (hp : 1 ≤ p) (k : ℕ) :
    eLpNorm (G.cutoffMaximal χ f) p volume ≤
      2 * dyadicWeight (2 / (p : ℝ)) k * G.scaledJetNorm χ f p 2 k := by
  have hJ₁ : Measurable (fun q : Parameters 2 2 =>
      ‖iteratedFDeriv ℝ 1 (fun u => G.cutoffAverage χ f (q.1, u)) q.2‖) := by
    simpa only [norm_iteratedFDeriv_one] using
      (contDiff_one_auxiliary_fderiv_of_contDiff_two hH).continuous.norm.measurable
  have hJ₂ := (continuous_auxiliaryJet_two_of_contDiff_two hH).measurable
  have hC : ∀ z : Base 2, ContDiff ℝ 2 (fun u => G.cutoffAverage χ f (z, u)) :=
    fun z => hH.comp ((contDiff_const (c := z)).prodMk contDiff_id)
  have hr : 0 < ((2 : ℝ) ^ (-1 : ℝ)) ^ k := by positivity
  have h := eLpNorm_iSup_aux_two_le_scaled_fullJet (volume : Measure (Base 2))
    hH.continuous.measurable hJ₁ hJ₂ hC p hp hr
  have hvol : (volume : Measure (Parameters 2 2)) =
      (volume : Measure (Base 2)).prod (volume : Measure (Aux 2)) := rfl
  rw [← hvol] at h
  have hw : ENNReal.ofReal (((2 : ℝ) ^ (-1 : ℝ)) ^ k) = dyadicWeight (-1) k := by
    rw [ENNReal.ofReal_pow (by positivity)]
    rfl
  rw [hw, dyadicWeight_rpow, ← ENNReal.rpow_natCast _ 2, dyadicWeight_rpow] at h
  have h₀ : G.auxiliaryJetNorm χ f p 0 = eLpNorm (G.cutoffAverage χ f) p volume := by
    simp only [Family.auxiliaryJetNorm, norm_iteratedFDeriv_zero, eLpNorm_norm]
  have hw₀ : dyadicWeight 0 k = 1 := by simp [dyadicWeight]
  simp only [Family.scaledJetNorm, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    zero_add, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, neg_zero, h₀, hw₀, one_mul]
  change eLpNorm (fun z : Base 2 => ⨆ u : Aux 2, ‖G.cutoffAverage χ f (z, u)‖ₑ) p volume ≤ _
  simpa only [neg_one_mul, neg_div, neg_neg, Nat.cast_ofNat, neg_mul, one_mul,
    Family.auxiliaryJetNorm] using h

/-- For two auxiliary parameters, joint `C²` regularity of actual band
averages suffices; the Sobolev estimate itself is proved here. -/
theorem Family.bandSobolevInput_aux_two_of_contDiff_bands (G : Family 2 2)
    (χ : Cutoff 2) (L : FrequencyCutoff) (p : ℝ≥0) (hp : 1 ≤ p)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hC : ∀ k f, Integrable f → MemLp f p volume →
      ContDiff ℝ 2 (G.cutoffAverage χ (L.band k f))) :
    BandSobolevInput G χ L p 2 δ := by
  refine ⟨2, ?_⟩
  intro k f hi hf
  calc
    _ ≤ 2 * dyadicWeight (2 / (p : ℝ)) k * G.scaledJetNorm χ (L.band k f) p 2 k :=
      G.cutoffMaximal_le_scaledJetNorm_aux_two_of_contDiff χ (L.band k f) (hC k f hi hf) p hp k
    _ ≤ 2 * dyadicWeight (2 / (p : ℝ) + δ) k * G.scaledJetNorm χ (L.band k f) p 2 k := by
      gcongr
      exact dyadicWeight_mono_exponent (le_add_of_nonneg_right hδ) k
    _ = _ := by simp

end PlanarNikodym
