import PlanarNikodym.Analysis.Sobolev.GeneralScaledSobolev
import PlanarNikodym.Analysis.Sobolev.BandSobolevTwoRegularity

/-! The general-dimensional full-jet inequality integrated over the centre
variables and applied to actual frequency-localized curve averages. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace PlanarNikodym

/-- Full auxiliary jets of a jointly smooth function are jointly continuous.
The identity is obtained from translation and composition with the actual
vertical inclusion, rather than from an additional measurability input. -/
theorem continuous_auxiliary_iteratedFDeriv_of_smooth
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {d : ℕ}
    {H : X × Aux d → ℂ} (hH : ContDiff ℝ ∞ H) (j : ℕ) :
    Continuous (fun q : X × Aux d => iteratedFDeriv ℝ j (fun u => H (q.1, u)) q.2) := by
  let T : Aux d →L[ℝ] X × Aux d := ContinuousLinearMap.inr ℝ X (Aux d)
  have heq : (fun q : X × Aux d => iteratedFDeriv ℝ j (fun u => H (q.1, u)) q.2) =
      fun q => (iteratedFDeriv ℝ j H q).compContinuousLinearMap (fun _ => T) := by
    funext q
    let a : X × Aux d := (q.1, 0)
    have hs := T.iteratedFDeriv_comp_right
      (contDiff_infty.mp (hH.comp ((contDiff_const (c := a)).add contDiff_id)) j) q.2 le_rfl
    simpa only [T, a, Function.comp_def, id_eq, ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk, zero_add, add_zero, iteratedFDeriv_comp_add_left] using hs
  rw [heq]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin j => T)).continuous.comp
    (contDiff_infty.mp hH j).continuous_iteratedFDeriv'

/-- The actual finite-dimensional tensor bound integrated over an arbitrary
base measure, with every full jet appearing on the right. -/
theorem eLpNorm_iSup_aux_le_scaled_fullJet (d : ℕ)
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {H : X × Aux d → ℂ}
    (hJ : ∀ j ∈ Finset.range (d + 1), Measurable (fun q : X × Aux d =>
      ‖iteratedFDeriv ℝ j (fun u => H (q.1, u)) q.2‖))
    (hC : ∀ x, ContDiff ℝ ∞ (fun u => H (x, u)))
    (p : ℝ≥0) (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x => ⨆ u : Aux d, ‖H (x, u)‖ₑ) p μ ≤
      (2 : ℝ≥0∞) ^ d * ENNReal.ofReal r ^ (-(d : ℝ) / (p : ℝ)) *
        ∑ j ∈ Finset.range (d + 1), ENNReal.ofReal r ^ j *
          eLpNorm (fun q : X × Aux d =>
            ‖iteratedFDeriv ℝ j (fun u => H (q.1, u)) q.2‖) p (μ.prod volume) :=
  eLpNorm_le_weighted_fiber_sum μ volume hJ
    ((2 : ℝ≥0∞) ^ d * ENNReal.ofReal r ^ (-(d : ℝ) / (p : ℝ)))
    (fun j => ENNReal.ofReal r ^ j) p hp
    (fun x => iSup_enorm_aux_le_scaled_fullJet d (hC x) p hp hr)

/-- The actual cutoff maximal function satisfies the correct scale exponent
in every auxiliary dimension. The full jet has order `d`. -/
theorem Family.cutoffMaximal_le_scaledJetNorm_of_smooth {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (f : Plane → ℂ) (hH : ContDiff ℝ ∞ (G.cutoffAverage χ f))
    (p : ℝ≥0) (hp : 1 ≤ p) (k : ℕ) :
    eLpNorm (G.cutoffMaximal χ f) p volume ≤
      (2 : ℝ≥0∞) ^ d * dyadicWeight ((d : ℝ) / (p : ℝ)) k *
        G.scaledJetNorm χ f p d k := by
  have hJ (j : ℕ) : Measurable (fun q : Parameters 2 d =>
      ‖iteratedFDeriv ℝ j (fun u => G.cutoffAverage χ f (q.1, u)) q.2‖) :=
    (continuous_auxiliary_iteratedFDeriv_of_smooth hH j).norm.measurable
  have hC (z : Base 2) : ContDiff ℝ ∞ (fun u => G.cutoffAverage χ f (z, u)) :=
    hH.comp ((contDiff_const (c := z)).prodMk contDiff_id)
  have hr : 0 < ((2 : ℝ) ^ (-1 : ℝ)) ^ k := by positivity
  have h := eLpNorm_iSup_aux_le_scaled_fullJet d (volume : Measure (Base 2))
    (fun j _ => hJ j) hC p hp hr
  have hvol : (volume : Measure (Parameters 2 d)) =
      (volume : Measure (Base 2)).prod (volume : Measure (Aux d)) := rfl
  rw [← hvol] at h
  have hw : ENNReal.ofReal (((2 : ℝ) ^ (-1 : ℝ)) ^ k) = dyadicWeight (-1) k := by
    rw [ENNReal.ofReal_pow (by positivity)]
    rfl
  rw [hw, dyadicWeight_rpow] at h
  have hwj (j : ℕ) : dyadicWeight (-1) k ^ j = dyadicWeight (-(j : ℝ)) k := by
    rw [← ENNReal.rpow_natCast, dyadicWeight_rpow]
    simp only [neg_one_mul]
  simp only [hwj, neg_one_mul, neg_div, neg_neg] at h
  exact h

theorem Family.scaledJetNorm_mono_order {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (f : Plane → ℂ) (p : ℝ≥0) {s t : ℕ} (hst : s ≤ t) (k : ℕ) :
    G.scaledJetNorm χ f p s k ≤ G.scaledJetNorm χ f p t k :=
  Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.add_le_add_right hst 1))

/-- The general-dimensional band Sobolev input is proved from actual smooth
geometry on the cutoff support. No Sobolev estimate, band regularity or
maximal-function estimate is assumed as an additional input. -/
theorem Family.bandSobolevInput_aux {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : 1 ≤ p) (δ : ℝ) (hδ : 0 ≤ δ) :
    BandSobolevInput G χ L p d δ := by
  refine ⟨(2 : ℝ≥0) ^ d, ?_⟩
  intro k f hi _
  have hH : ContDiff ℝ ∞ (G.cutoffAverage χ (L.band k f)) :=
    G.bandAverage_contDiff χ hχ hc hγ L k hi
  calc
    _ ≤ (2 : ℝ≥0∞) ^ d * dyadicWeight ((d : ℝ) / (p : ℝ)) k *
        G.scaledJetNorm χ (L.band k f) p d k :=
      G.cutoffMaximal_le_scaledJetNorm_of_smooth χ (L.band k f) hH p hp k
    _ ≤ (2 : ℝ≥0∞) ^ d * dyadicWeight ((d : ℝ) / (p : ℝ) + δ) k *
        G.scaledJetNorm χ (L.band k f) p d k := by
      gcongr
      exact dyadicWeight_mono_exponent (le_add_of_nonneg_right hδ) k
    _ = _ := by simp

theorem Family.bandSobolevInput_aux_of_order_ge {d s : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : 1 ≤ p) (δ : ℝ) (hδ : 0 ≤ δ) (hds : d ≤ s) :
    BandSobolevInput G χ L p s δ := by
  obtain ⟨C, hC⟩ := G.bandSobolevInput_aux χ hχ hc hγ L p hp δ hδ
  refine ⟨C, ?_⟩
  intro k f hi hf
  exact (hC k f hi hf).trans (by
    gcongr
    exact G.scaledJetNorm_mono_order χ (L.band k f) p hds k)

end PlanarNikodym
