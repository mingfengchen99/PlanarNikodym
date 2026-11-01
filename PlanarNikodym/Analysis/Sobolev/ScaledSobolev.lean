import PlanarNikodym.Analysis.Maximal.LocalSmoothing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Constructions.Pi

/-! Concrete one-dimensional parameter Sobolev estimates.  The bounds use the
actual derivative of the function and its pointwise supremum. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

section OneDimension
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fundamental theorem of calculus controls oscillation anywhere in a
closed interval by the integral of the actual derivative on that interval. -/
theorem enorm_sub_le_lintegral_deriv_on_interval {f : ℝ → E}
    (hf : ContDiff ℝ 1 f) {a b x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x - f y‖ₑ ≤ ∫⁻ t in Icc a b, ‖deriv f t‖ₑ := by
  rcases le_total y x with hyx | hxy
  · exact (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hf.contDiffOn hyx).trans
      (lintegral_mono_set (Icc_subset_Icc hy.1 hx.2))
  · rw [enorm_sub_rev]
    exact (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hf.contDiffOn hxy).trans
      (lintegral_mono_set (Icc_subset_Icc hx.1 hy.2))

/-- The local `W¹,¹` estimate, with its exact interval-length normalization.
No compact-support or integrability assumption is needed: all norms are extended
nonnegative numbers. -/
theorem enorm_le_interval_average_add_deriv {f : ℝ → E}
    (hf : ContDiff ℝ 1 f) {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    ‖f x‖ₑ ≤ (∫⁻ t in Icc a b, ‖f t‖ₑ) / volume (Icc a b) +
      ∫⁻ t in Icc a b, ‖deriv f t‖ₑ := by
  obtain ⟨y, hy, hfy⟩ := exists_le_setLAverage
    (show volume (Icc a b) ≠ 0 by simpa using hab)
    (isCompact_Icc.measure_lt_top (μ := volume)).ne
    hf.continuous.enorm.measurable.aemeasurable.restrict
  rw [setLAverage_eq] at hfy
  calc
    ‖f x‖ₑ = ‖f x - f y + f y‖ₑ := by congr 1; abel
    _ ≤ ‖f x - f y‖ₑ + ‖f y‖ₑ := enorm_add_le _ _
    _ ≤ (∫⁻ t in Icc a b, ‖deriv f t‖ₑ) +
        (∫⁻ t in Icc a b, ‖f t‖ₑ) / volume (Icc a b) :=
      add_le_add (enorm_sub_le_lintegral_deriv_on_interval hf hx hy) hfy
    _ = _ := add_comm _ _

/-- The first-order one-dimensional Sobolev estimate on an interval, for every
finite exponent at least one.  Both powers of the length are explicit. -/
theorem enorm_le_interval_eLpNorm_add_deriv {f : ℝ → E}
    (hf : ContDiff ℝ 1 f) {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b)
    (p : ℝ≥0) (hp : 1 ≤ p) :
    ‖f x‖ₑ ≤ volume (Icc a b) ^ (-1 / (p : ℝ)) *
        eLpNorm f p (volume.restrict (Icc a b)) +
      volume (Icc a b) ^ (1 - 1 / (p : ℝ)) *
        eLpNorm (deriv f) p (volume.restrict (Icc a b)) := by
  have hm0 : volume (Icc a b) ≠ 0 := by simpa using hab
  have hmt : volume (Icc a b) ≠ ∞ := (isCompact_Icc.measure_lt_top (μ := volume)).ne
  have hfp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (1 : ℝ≥0∞) ≤ p by exact_mod_cast hp)
    hf.continuous.aestronglyMeasurable.restrict (μ := volume.restrict (Icc a b))
  have hdp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (1 : ℝ≥0∞) ≤ p by exact_mod_cast hp)
    hf.continuous_deriv_one.aestronglyMeasurable.restrict
    (μ := volume.restrict (Icc a b))
  simp only [eLpNorm_one_eq_lintegral_enorm, ENNReal.toReal_one, ENNReal.coe_toReal,
    div_one, Measure.restrict_apply_univ] at hfp hdp
  have hscale (N : ℝ≥0∞) :
      (N * volume (Icc a b) ^ (1 - 1 / (p : ℝ))) / volume (Icc a b) =
        volume (Icc a b) ^ (-1 / (p : ℝ)) * N := by
    rw [ENNReal.div_eq_inv_mul, ← ENNReal.rpow_neg_one]
    calc
      _ = N * (volume (Icc a b) ^ (1 - 1 / (p : ℝ)) *
          volume (Icc a b) ^ (-1 : ℝ)) := by ac_rfl
      _ = N * volume (Icc a b) ^ (-1 / (p : ℝ)) := by
        rw [← ENNReal.rpow_add _ _ hm0 hmt]
        congr 1
        congr 1
        ring
      _ = _ := mul_comm _ _
  calc
    ‖f x‖ₑ ≤ (∫⁻ t in Icc a b, ‖f t‖ₑ) / volume (Icc a b) +
        ∫⁻ t in Icc a b, ‖deriv f t‖ₑ :=
      enorm_le_interval_average_add_deriv hf hab hx
    _ ≤ (eLpNorm f p (volume.restrict (Icc a b)) *
        volume (Icc a b) ^ (1 - 1 / (p : ℝ))) / volume (Icc a b) +
        eLpNorm (deriv f) p (volume.restrict (Icc a b)) *
          volume (Icc a b) ^ (1 - 1 / (p : ℝ)) :=
      add_le_add (ENNReal.div_le_div_right hfp _) hdp
    _ = _ := by rw [hscale, mul_comm (eLpNorm (deriv f) _ _)]

/-- A global pointwise Sobolev estimate with an arbitrary positive length.
Taking length `2⁻ᵏ` is the frequency-normalized estimate used for dyadic bands. -/
theorem enorm_le_scaled_eLpNorm_add_deriv {f : ℝ → E}
    (hf : ContDiff ℝ 1 f) (p : ℝ≥0) (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ‖f x‖ₑ ≤ ENNReal.ofReal r ^ (-1 / (p : ℝ)) *
      (eLpNorm f p volume + ENNReal.ofReal r * eLpNorm (deriv f) p volume) := by
  have hlocal := enorm_le_interval_eLpNorm_add_deriv hf
    (show x < x + r by linarith) (show x ∈ Icc x (x + r) by constructor <;> linarith) p hp
  have hm : volume (Icc x (x + r)) = ENNReal.ofReal r := by simp
  rw [hm] at hlocal
  have hr0 : ENNReal.ofReal r ≠ 0 := by positivity
  have hexp : ENNReal.ofReal r ^ (1 - 1 / (p : ℝ)) =
      ENNReal.ofReal r ^ (-1 / (p : ℝ)) * ENNReal.ofReal r := by
    calc
      _ = ENNReal.ofReal r ^ (-1 / (p : ℝ) + 1) := by congr 1; ring
      _ = _ := by rw [ENNReal.rpow_add _ _ hr0 ENNReal.ofReal_ne_top]; simp
  calc
    ‖f x‖ₑ ≤ _ := hlocal
    _ ≤ ENNReal.ofReal r ^ (-1 / (p : ℝ)) * eLpNorm f p volume +
        ENNReal.ofReal r ^ (1 - 1 / (p : ℝ)) * eLpNorm (deriv f) p volume := by
      gcongr <;> exact Measure.restrict_le_self
    _ = _ := by rw [hexp, mul_add, mul_assoc]

/-- Pointwise suprema, rather than essential suprema, satisfy the scaled
one-dimensional estimate for a continuously differentiable function. -/
theorem iSup_enorm_le_scaled_eLpNorm_add_deriv {f : ℝ → E}
    (hf : ContDiff ℝ 1 f) (p : ℝ≥0) (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) :
    (⨆ x : ℝ, ‖f x‖ₑ) ≤ ENNReal.ofReal r ^ (-1 / (p : ℝ)) *
      (eLpNorm f p volume + ENNReal.ofReal r * eLpNorm (deriv f) p volume) :=
  iSup_le (enorm_le_scaled_eLpNorm_add_deriv hf p hp hr)

end OneDimension

section FiberNorms
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) (ν : Measure Y) [SFinite ν]

/-- Taking the finite `Lp` norm of a measurable fibre gives a measurable
extended-nonnegative function of the base point. -/
theorem measurable_fiber_eLpNorm {F : X × Y → ℂ} (hF : Measurable F)
    (p : ℝ≥0) (hp : p ≠ 0) :
    Measurable (fun x => eLpNorm (fun y => F (x, y)) p ν) := by
  simp_rw [eLpNorm_nnreal_eq_lintegral hp]
  exact ((hF.enorm.pow_const (p : ℝ)).lintegral_prod_right').pow_const _

/-- Fubini's theorem for equal finite exponents in the two factors. -/
theorem eLpNorm_fiber_eLpNorm {F : X × Y → ℂ} (hF : Measurable F)
    (p : ℝ≥0) (hp : p ≠ 0) :
    eLpNorm (fun x => eLpNorm (fun y => F (x, y)) p ν) p μ =
      eLpNorm F p (μ.prod ν) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  simp_rw [eLpNorm_nnreal_eq_lintegral hp, enorm_eq_self,
    ← ENNReal.rpow_mul, one_div_mul_cancel hpR, ENNReal.rpow_one]
  rw [← lintegral_prod _ (hF.enorm.pow_const (p : ℝ)).aemeasurable]

end FiberNorms

section IntegratedOneDimension
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Homogeneity of finite `Lp` seminorms for measurable nonnegative extended
functions, including infinite constants and infinite-valued functions. -/
theorem eLpNorm_ennreal_const_mul {N : X → ℝ≥0∞} (hN : Measurable N)
    (p : ℝ≥0) (hp : p ≠ 0) (c : ℝ≥0∞) :
    eLpNorm (fun x => c * N x) p μ = c * eLpNorm N p μ := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  simp_rw [eLpNorm_nnreal_eq_lintegral hp, enorm_eq_self,
    ENNReal.mul_rpow_of_nonneg _ _ p.coe_nonneg]
  rw [lintegral_const_mul _ (hN.pow_const (p : ℝ)),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr p.coe_nonneg),
    ← ENNReal.rpow_mul, mul_one_div_cancel hpR, ENNReal.rpow_one]

/-- The scaled one-parameter Sobolev bound integrated over an arbitrary base
measure space.  This is the full mixed-norm inequality, not a pointwise-only
estimate. -/
theorem eLpNorm_iSup_enorm_le_scaled_eLpNorm_add_deriv
    {F : X × ℝ → ℂ} (hF : Measurable F)
    (hFD : Measurable (fun q : X × ℝ => deriv (fun u => F (q.1, u)) q.2))
    (hC : ∀ x, ContDiff ℝ 1 (fun u => F (x, u)))
    (p : ℝ≥0) (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x => ⨆ u : ℝ, ‖F (x, u)‖ₑ) p μ ≤
      ENNReal.ofReal r ^ (-1 / (p : ℝ)) *
        (eLpNorm F p (μ.prod volume) + ENNReal.ofReal r *
          eLpNorm (fun q : X × ℝ => deriv (fun u => F (q.1, u)) q.2)
            p (μ.prod volume)) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  let A : X → ℝ≥0∞ := fun x => eLpNorm (fun u => F (x, u)) p volume
  let B : X → ℝ≥0∞ := fun x => eLpNorm (fun u => deriv (fun v => F (x, v)) u) p volume
  have hA : Measurable A := measurable_fiber_eLpNorm volume hF p hp0
  have hB : Measurable B := measurable_fiber_eLpNorm volume hFD p hp0
  have hm : ∀ x, (⨆ u : ℝ, ‖F (x, u)‖ₑ) ≤
      ENNReal.ofReal r ^ (-1 / (p : ℝ)) * (A x + ENNReal.ofReal r * B x) :=
    fun x => iSup_enorm_le_scaled_eLpNorm_add_deriv (hC x) p hp hr
  calc
    _ ≤ eLpNorm (fun x => ENNReal.ofReal r ^ (-1 / (p : ℝ)) *
        (A x + ENNReal.ofReal r * B x)) p μ :=
      eLpNorm_mono_enorm (by simpa only [enorm_eq_self] using hm)
    _ = ENNReal.ofReal r ^ (-1 / (p : ℝ)) *
        eLpNorm (fun x => A x + ENNReal.ofReal r * B x) p μ := by
      exact eLpNorm_ennreal_const_mul μ (hA.add (measurable_const.mul hB)) p hp0 _
    _ ≤ ENNReal.ofReal r ^ (-1 / (p : ℝ)) *
        (eLpNorm A p μ + eLpNorm (fun x => ENNReal.ofReal r * B x) p μ) := by
      gcongr
      exact eLpNorm_add_le hA.stronglyMeasurable.aestronglyMeasurable
        (measurable_const.mul hB).stronglyMeasurable.aestronglyMeasurable
        (show (1 : ℝ≥0∞) ≤ p by exact_mod_cast hp)
    _ = _ := by
      rw [eLpNorm_ennreal_const_mul μ hB p hp0]
      rw [eLpNorm_fiber_eLpNorm μ volume hF p hp0,
        eLpNorm_fiber_eLpNorm μ volume hFD p hp0]

end IntegratedOneDimension

section AuxiliaryOne
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]

/-- The one-parameter estimate in the project's actual auxiliary coordinates
`Aux 1`, with the norm of the actual Fréchet derivative. -/
theorem eLpNorm_iSup_aux_one_le_scaled_eLpNorm_add_fderiv
    {H : X × Aux 1 → ℂ} (hH : Measurable H)
    (hHD : Measurable (fun q : X × Aux 1 => fderiv ℝ (fun u => H (q.1, u)) q.2))
    (hC : ∀ x, ContDiff ℝ 1 (fun u => H (x, u)))
    (p : ℝ≥0) (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x => ⨆ u : Aux 1, ‖H (x, u)‖ₑ) p μ ≤
      ENNReal.ofReal r ^ (-1 / (p : ℝ)) *
        (eLpNorm H p (μ.prod volume) + ENNReal.ofReal r *
          eLpNorm (fun q : X × Aux 1 => ‖fderiv ℝ (fun u => H (q.1, u)) q.2‖)
            p (μ.prod volume)) := by
  let c : ℝ →L[ℝ] Aux 1 := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ ℝ)
  let P : X × ℝ → X × Aux 1 := fun q => (q.1, c q.2)
  let D : X × Aux 1 → Aux 1 →L[ℝ] ℂ := fun q => fderiv ℝ (fun u => H (q.1, u)) q.2
  have hc : MeasurePreserving c volume volume := by
    exact (volume_preserving_funUnique (Fin 1) ℝ).symm _
  have hP : MeasurePreserving P (μ.prod volume) (μ.prod volume) :=
    (MeasurePreserving.id μ).prod hc
  have hd (x : X) (u : ℝ) :
      deriv (fun v => H (x, c v)) u = D (P (x, u)) (c 1) := by
    exact (((hC x).differentiable one_ne_zero (c u)).hasFDerivAt.comp_hasDerivAt
      u c.hasFDerivAt.hasDerivAt).deriv
  have hFD : Measurable (fun q : X × ℝ => deriv (fun u => H (q.1, c u)) q.2) := by
    have heq : (fun q : X × ℝ => deriv (fun u => H (q.1, c u)) q.2) =
        (fun q : X × ℝ => D (P q) (c 1)) := funext (fun q => hd q.1 q.2)
    rw [heq]
    have hm : Measurable (D ∘ P) := hHD.comp hP.measurable
    exact (show Continuous (fun L : Aux 1 →L[ℝ] ℂ => L (c 1)) by fun_prop).measurable.comp hm
  have hsup (x : X) : (⨆ u : ℝ, ‖H (x, c u)‖ₑ) =
      ⨆ u : Aux 1, ‖H (x, u)‖ₑ := by
    apply le_antisymm
    · exact iSup_le (fun u => le_iSup_of_le (c u) le_rfl)
    · refine iSup_le (fun u => ?_)
      have hu : c (u 0) = u := by
        funext i
        exact congrArg u (Subsingleton.elim _ _)
      rw [← hu]
      exact le_iSup_of_le (u 0) le_rfl
  have h := eLpNorm_iSup_enorm_le_scaled_eLpNorm_add_deriv μ
    (hH.comp hP.measurable) hFD (fun x => (hC x).comp c.contDiff) p hp hr
  simp only [Function.comp_def, P] at h
  rw [show (fun x => ⨆ u : ℝ, ‖H (x, c u)‖ₑ) =
    (fun x => ⨆ u : Aux 1, ‖H (x, u)‖ₑ) from funext hsup] at h
  have hzero : eLpNorm (fun q : X × ℝ => H (q.1, c q.2)) p (μ.prod volume) =
      eLpNorm H p (μ.prod volume) :=
    eLpNorm_comp_measurePreserving hH.stronglyMeasurable.aestronglyMeasurable hP
  have hone : eLpNorm (fun q : X × ℝ => deriv (fun u => H (q.1, c u)) q.2)
      p (μ.prod volume) ≤ eLpNorm (fun q : X × Aux 1 => ‖D q‖) p (μ.prod volume) := by
    calc
      _ ≤ eLpNorm (fun q : X × ℝ => ‖D (P q)‖) p (μ.prod volume) := by
        apply eLpNorm_mono_real
        intro q
        rw [hd]
        exact (D (P q)).unit_le_opNorm (c 1) (by
          change ‖(fun _ : Fin 1 => (1 : ℝ))‖ ≤ 1
          simp)
      _ = _ := eLpNorm_comp_measurePreserving (f := P) (g := fun q : X × Aux 1 => ‖D q‖)
        hHD.norm.stronglyMeasurable.aestronglyMeasurable hP
  rw [hzero] at h
  exact h.trans (by gcongr)

end AuxiliaryOne

/-- In auxiliary dimension zero, the supremum is a single value and the
auxiliary volume is a Dirac measure.  This equality needs no measurability
assumption on the function. -/
theorem eLpNorm_iSup_aux_zero (H : Parameters 2 0 → ℂ) (p : ℝ≥0) :
    eLpNorm (fun z : Base 2 => ⨆ u : Aux 0, ‖H (z, u)‖ₑ) p volume =
      eLpNorm H p volume := by
  have hsup : (fun z : Base 2 => ⨆ u : Aux 0, ‖H (z, u)‖ₑ) =
      fun z => ‖H (z, 0)‖ₑ := by
    funext z
    apply le_antisymm
    · exact iSup_le (fun u => by rw [Subsingleton.elim u 0])
    · exact le_iSup_of_le 0 le_rfl
  rw [hsup, eLpNorm_enorm]
  change eLpNorm (fun z : Base 2 => H (z, 0)) p volume =
    eLpNorm H p (volume.prod (volume : Measure (Aux 0)))
  rw [Measure.volume_pi_eq_dirac (0 : Aux 0), Measure.prod_dirac]
  exact (measurableEmbedding_prod_mk_right (0 : Aux 0)).eLpNorm_map_measure.symm

/-- Real powers of a dyadic weight multiply its scale exponent. -/
theorem dyadicWeight_rpow (a b : ℝ) (k : ℕ) :
    dyadicWeight a k ^ b = dyadicWeight (a * b) k := by
  have hw (c : ℝ) : dyadicWeight c k = ENNReal.ofReal 2 ^ ((k : ℝ) * c) := by
    unfold dyadicWeight
    rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2),
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    ring
  rw [hw, hw, ← ENNReal.rpow_mul]
  congr 1
  ring

/-- Increasing the exponent increases every dyadic weight. -/
theorem dyadicWeight_mono_exponent {a b : ℝ} (hab : a ≤ b) (k : ℕ) :
    dyadicWeight a k ≤ dyadicWeight b k := by
  unfold dyadicWeight
  gcongr
  norm_num

/-- Auxiliary dimension zero requires no Sobolev theorem.  Its band Sobolev
input is unconditional, even without regularity hypotheses on the average. -/
theorem Family.bandSobolevInput_aux_zero (G : Family 2 0) (χ : Cutoff 0)
    (L : FrequencyCutoff) (p : ℝ≥0) (s : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    BandSobolevInput G χ L p s δ := by
  refine ⟨1, ?_⟩
  intro k f _ _
  have hweight : 1 ≤ dyadicWeight δ k := by
    simpa [dyadicWeight] using dyadicWeight_mono_exponent hδ k
  calc
    eLpNorm (G.cutoffMaximal χ (L.band k f)) p volume =
        eLpNorm (G.cutoffAverage χ (L.band k f)) p volume :=
      eLpNorm_iSup_aux_zero _ p
    _ ≤ G.scaledJetNorm χ (L.band k f) p s k := G.averageNorm_le_scaledJetNorm _ _ _ _ _
    _ ≤ dyadicWeight δ k * G.scaledJetNorm χ (L.band k f) p s k := by
      simpa [mul_comm] using mul_le_mul_right hweight (G.scaledJetNorm χ (L.band k f) p s k)
    _ = _ := by simp

/-- The exact dyadic version of the one-parameter mixed-norm Sobolev bound.
The constant is one, and there is no additional exponent loss. -/
theorem eLpNorm_iSup_enorm_le_dyadic_eLpNorm_add_deriv
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : X × ℝ → ℂ} (hF : Measurable F)
    (hFD : Measurable (fun q : X × ℝ => deriv (fun u => F (q.1, u)) q.2))
    (hC : ∀ x, ContDiff ℝ 1 (fun u => F (x, u)))
    (p : ℝ≥0) (hp : 1 ≤ p) (k : ℕ) :
    eLpNorm (fun x => ⨆ u : ℝ, ‖F (x, u)‖ₑ) p μ ≤
      dyadicWeight (1 / (p : ℝ)) k *
        (eLpNorm F p (μ.prod volume) + dyadicWeight (-1) k *
          eLpNorm (fun q : X × ℝ => deriv (fun u => F (q.1, u)) q.2)
            p (μ.prod volume)) := by
  have hr : 0 < ((2 : ℝ) ^ (-1 : ℝ)) ^ k := by positivity
  have h := eLpNorm_iSup_enorm_le_scaled_eLpNorm_add_deriv μ hF hFD hC p hp hr
  have hw : ENNReal.ofReal (((2 : ℝ) ^ (-1 : ℝ)) ^ k) = dyadicWeight (-1) k := by
    rw [ENNReal.ofReal_pow (by positivity)]
    rfl
  rw [hw, dyadicWeight_rpow] at h
  simpa only [neg_one_mul, neg_div, neg_neg] using h

/-- The project's one-auxiliary-variable cutoff maximal function obeys the
scaled Sobolev estimate whenever its actual average is `C¹` in that variable
and the average and its actual partial derivative are jointly measurable. -/
theorem Family.cutoffMaximal_le_scaledJetNorm_aux_one (G : Family 2 1)
    (χ : Cutoff 1) (f : Plane → ℂ)
    (hA : Measurable (G.cutoffAverage χ f))
    (hD : Measurable (fun q : Parameters 2 1 =>
      fderiv ℝ (fun u => G.cutoffAverage χ f (q.1, u)) q.2))
    (hC : ∀ z : Base 2, ContDiff ℝ 1 (fun u => G.cutoffAverage χ f (z, u)))
    (p : ℝ≥0) (hp : 1 ≤ p) (k : ℕ) :
    eLpNorm (G.cutoffMaximal χ f) p volume ≤
      dyadicWeight (1 / (p : ℝ)) k * G.scaledJetNorm χ f p 1 k := by
  have hr : 0 < ((2 : ℝ) ^ (-1 : ℝ)) ^ k := by positivity
  have h := eLpNorm_iSup_aux_one_le_scaled_eLpNorm_add_fderiv
    (volume : Measure (Base 2)) hA hD hC p hp hr
  have hvol : (volume : Measure (Parameters 2 1)) =
      (volume : Measure (Base 2)).prod (volume : Measure (Aux 1)) := rfl
  rw [← hvol] at h
  have hw : ENNReal.ofReal (((2 : ℝ) ^ (-1 : ℝ)) ^ k) = dyadicWeight (-1) k := by
    rw [ENNReal.ofReal_pow (by positivity)]
    rfl
  rw [hw, dyadicWeight_rpow] at h
  have hj : G.scaledJetNorm χ f p 1 k =
      eLpNorm (G.cutoffAverage χ f) p volume + dyadicWeight (-1) k *
        eLpNorm (fun q : Parameters 2 1 =>
          ‖fderiv ℝ (fun u => G.cutoffAverage χ f (q.1, u)) q.2‖) p volume := by
    have h0 : G.auxiliaryJetNorm χ f p 0 = eLpNorm (G.cutoffAverage χ f) p volume := by
      simp only [auxiliaryJetNorm, norm_iteratedFDeriv_zero, eLpNorm_norm]
    have h1 : G.auxiliaryJetNorm χ f p 1 = eLpNorm (fun q : Parameters 2 1 =>
        ‖fderiv ℝ (fun u => G.cutoffAverage χ f (q.1, u)) q.2‖) p volume := by
      simp only [auxiliaryJetNorm, norm_iteratedFDeriv_one]
    have hw0 : dyadicWeight 0 k = 1 := by simp [dyadicWeight]
    simp only [scaledJetNorm, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      zero_add, Nat.cast_zero, Nat.cast_one, neg_zero, h0, h1, hw0, one_mul]
  rw [hj]
  change eLpNorm (fun z : Base 2 => ⨆ u : Aux 1, ‖G.cutoffAverage χ f (z, u)‖ₑ) p volume ≤ _
  simpa only [neg_one_mul, neg_div, neg_neg] using h

/-- In dimension one the remaining requirement for the actual band Sobolev
input is regularity and measurability of the frequency-localized averages.
There is no additional analytic estimate among the assumptions. -/
theorem Family.bandSobolevInput_aux_one_of_regular_bands (G : Family 2 1)
    (χ : Cutoff 1) (L : FrequencyCutoff) (p : ℝ≥0) (hp : 1 ≤ p)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hA : ∀ k f, Integrable f → MemLp f p volume →
      Measurable (G.cutoffAverage χ (L.band k f)))
    (hD : ∀ k f, Integrable f → MemLp f p volume →
      Measurable (fun q : Parameters 2 1 =>
        fderiv ℝ (fun u => G.cutoffAverage χ (L.band k f) (q.1, u)) q.2))
    (hC : ∀ k f, Integrable f → MemLp f p volume → ∀ z : Base 2,
      ContDiff ℝ 1 (fun u => G.cutoffAverage χ (L.band k f) (z, u))) :
    BandSobolevInput G χ L p 1 δ := by
  refine ⟨1, ?_⟩
  intro k f hi hf
  calc
    _ ≤ dyadicWeight (1 / (p : ℝ)) k * G.scaledJetNorm χ (L.band k f) p 1 k :=
      G.cutoffMaximal_le_scaledJetNorm_aux_one χ (L.band k f)
        (hA k f hi hf) (hD k f hi hf) (hC k f hi hf) p hp k
    _ ≤ dyadicWeight (1 / (p : ℝ) + δ) k * G.scaledJetNorm χ (L.band k f) p 1 k := by
      gcongr
      exact dyadicWeight_mono_exponent (le_add_of_nonneg_right hδ) k
    _ = _ := by simp

/-- A jointly `C¹` function has a continuous actual derivative in its
auxiliary coordinates. -/
theorem continuous_auxiliary_fderiv_of_contDiff {n d : ℕ}
    {H : Parameters n d → ℂ} (hH : ContDiff ℝ 1 H) :
    Continuous (fun q : Parameters n d => fderiv ℝ (fun u => H (q.1, u)) q.2) := by
  have heq : (fun q : Parameters n d => fderiv ℝ (fun u => H (q.1, u)) q.2) =
      fun q => (fderiv ℝ H q).comp (ContinuousLinearMap.inr ℝ (Base n) (Aux d)) := by
    funext q
    have hJ : HasFDerivAt (fun u : Aux d => (q.1, u))
        (ContinuousLinearMap.inr ℝ (Base n) (Aux d)) q.2 :=
      (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
    exact ((hH.differentiable one_ne_zero q).hasFDerivAt.comp q.2 hJ).fderiv
  rw [heq]
  exact (hH.continuous_fderiv one_ne_zero).clm_comp_const _

/-- Joint `C¹` regularity alone supplies every regularity hypothesis of the
one-auxiliary-variable Sobolev estimate. -/
theorem Family.cutoffMaximal_le_scaledJetNorm_aux_one_of_contDiff
    (G : Family 2 1) (χ : Cutoff 1) (f : Plane → ℂ)
    (hC : ContDiff ℝ 1 (G.cutoffAverage χ f)) (p : ℝ≥0) (hp : 1 ≤ p) (k : ℕ) :
    eLpNorm (G.cutoffMaximal χ f) p volume ≤
      dyadicWeight (1 / (p : ℝ)) k * G.scaledJetNorm χ f p 1 k := by
  apply G.cutoffMaximal_le_scaledJetNorm_aux_one χ f hC.continuous.measurable
    (continuous_auxiliary_fderiv_of_contDiff hC).measurable
    (fun z => hC.comp ((contDiff_const (c := z)).prodMk contDiff_id)) p hp k

/-- For one auxiliary parameter, proving joint `C¹` regularity of the
frequency-localized averages suffices to construct the Sobolev input. -/
theorem Family.bandSobolevInput_aux_one_of_contDiff_bands (G : Family 2 1)
    (χ : Cutoff 1) (L : FrequencyCutoff) (p : ℝ≥0) (hp : 1 ≤ p)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hC : ∀ k f, Integrable f → MemLp f p volume →
      ContDiff ℝ 1 (G.cutoffAverage χ (L.band k f))) :
    BandSobolevInput G χ L p 1 δ := by
  apply G.bandSobolevInput_aux_one_of_regular_bands χ L p hp δ hδ
  · intro k f hi hf
    exact (hC k f hi hf).continuous.measurable
  · intro k f hi hf
    exact (continuous_auxiliary_fderiv_of_contDiff (hC k f hi hf)).measurable
  · intro k f hi hf z
    exact (hC k f hi hf).comp ((contDiff_const (c := z)).prodMk contDiff_id)

/-- At every exponent used by Theorem 2.1, a first auxiliary derivative has
order strictly larger than `d/p`. -/
theorem smoothingThreshold_sobolev_order_one (d : ℕ) (p : ℝ≥0)
    (hp : smoothingThreshold d ≤ p) : (d : ℝ) / (p : ℝ) < 1 := by
  have hdim : (d : ℝ) < (smoothingThreshold d : ℝ) := by
    simp only [smoothingThreshold, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast,
      NNReal.coe_one, NNReal.coe_ofNat]
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hpp : (d : ℝ) < (p : ℝ) := hdim.trans_le (by exact_mod_cast hp)
  exact (div_lt_one (lt_of_le_of_lt (Nat.cast_nonneg d) hpp)).mpr hpp

end PlanarNikodym
