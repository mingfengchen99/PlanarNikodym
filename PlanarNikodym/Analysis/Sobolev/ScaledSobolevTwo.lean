import PlanarNikodym.Analysis.Sobolev.ScaledSobolev

/-! Tensorizing the one-dimensional estimate gives a genuine two-dimensional
Sobolev inequality with the correct scale exponent, using actual mixed
derivatives.  This is a higher-derivative route to the high-dimensional bound. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal

namespace PlanarNikodym

/-- Actual derivative in the first real coordinate. -/
def partialFirst (F : Plane → ℂ) (q : Plane) : ℂ := deriv (fun u => F (u, q.2)) q.1

/-- Actual derivative in the second real coordinate. -/
def partialSecond (F : Plane → ℂ) (q : Plane) : ℂ := deriv (fun u => F (q.1, u)) q.2

/-- A two-dimensional scaled Sobolev estimate, proved by two applications of
the one-dimensional theorem.  Its assumptions concern actual regularity and
measurability of the function and its actual mixed derivatives. -/
theorem iSup_enorm_le_scaled_eLpNorm_two {F : Plane → ℂ}
    (hF : Measurable F) (hF₁ : Measurable (partialFirst F))
    (hF₂ : Measurable (partialSecond F))
    (hF₂₁ : Measurable (partialSecond (partialFirst F)))
    (hC₁ : ∀ v : ℝ, ContDiff ℝ 1 (fun u => F (u, v)))
    (hC₂ : ∀ u : ℝ, ContDiff ℝ 1 (fun v => F (u, v)))
    (hC₂₁ : ∀ u : ℝ, ContDiff ℝ 1 (fun v => partialFirst F (u, v)))
    (p : ℝ≥0) (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) :
    (⨆ q : Plane, ‖F q‖ₑ) ≤ ENNReal.ofReal r ^ (-2 / (p : ℝ)) *
      (eLpNorm F p volume + ENNReal.ofReal r * eLpNorm (partialSecond F) p volume +
        ENNReal.ofReal r * eLpNorm (partialFirst F) p volume +
        ENNReal.ofReal r ^ 2 * eLpNorm (partialSecond (partialFirst F)) p volume) := by
  let A : ℝ≥0∞ := ENNReal.ofReal r ^ (-1 / (p : ℝ))
  let S₀ : ℝ → ℝ≥0∞ := fun u => ⨆ v : ℝ, ‖F (u, v)‖ₑ
  let S₁ : ℝ → ℝ≥0∞ := fun u => ⨆ v : ℝ, ‖partialFirst F (u, v)‖ₑ
  have hzero := eLpNorm_iSup_enorm_le_scaled_eLpNorm_add_deriv volume hF hF₂ hC₂ p hp hr
  have hone := eLpNorm_iSup_enorm_le_scaled_eLpNorm_add_deriv volume hF₁ hF₂₁ hC₂₁ p hp hr
  have hvol : (volume : Measure Plane) = (volume : Measure ℝ).prod volume := rfl
  rw [← hvol] at hzero hone
  have hA : A * A = ENNReal.ofReal r ^ (-2 / (p : ℝ)) := by
    change ENNReal.ofReal r ^ (-1 / (p : ℝ)) * ENNReal.ofReal r ^ (-1 / (p : ℝ)) = _
    rw [← ENNReal.rpow_add _ _ (by positivity) ENNReal.ofReal_ne_top]
    congr 1
    ring
  apply iSup_le
  intro q
  have hbase : eLpNorm (fun u : ℝ => F (u, q.2)) p volume ≤ eLpNorm S₀ p volume := by
    apply eLpNorm_mono_enorm
    intro u
    simp only [enorm_eq_self]
    exact le_iSup_of_le q.2 le_rfl
  have hfirst : eLpNorm (deriv (fun u : ℝ => F (u, q.2))) p volume ≤
      eLpNorm S₁ p volume := by
    apply eLpNorm_mono_enorm
    intro u
    simp only [enorm_eq_self]
    exact le_iSup_of_le q.2 le_rfl
  calc
    ‖F q‖ₑ ≤ A * (eLpNorm (fun u => F (u, q.2)) p volume +
        ENNReal.ofReal r * eLpNorm (deriv (fun u => F (u, q.2))) p volume) :=
      enorm_le_scaled_eLpNorm_add_deriv (hC₁ q.2) p hp hr q.1
    _ ≤ A * (eLpNorm S₀ p volume + ENNReal.ofReal r * eLpNorm S₁ p volume) := by
      gcongr
    _ ≤ A * (A * (eLpNorm F p volume + ENNReal.ofReal r *
          eLpNorm (partialSecond F) p volume) + ENNReal.ofReal r *
        (A * (eLpNorm (partialFirst F) p volume + ENNReal.ofReal r *
          eLpNorm (partialSecond (partialFirst F)) p volume))) := by
      gcongr
      · exact hzero
      · exact hone
    _ = A * A * (eLpNorm F p volume + ENNReal.ofReal r * eLpNorm (partialSecond F) p volume +
        ENNReal.ofReal r * eLpNorm (partialFirst F) p volume +
        ENNReal.ofReal r ^ 2 * eLpNorm (partialSecond (partialFirst F)) p volume) := by ring
    _ = _ := by rw [hA]

/-- Dyadic scaling in two auxiliary real coordinates: the loss is exactly
`2^(2k/p)`, while each actual derivative carries one factor `2^(-k)`. -/
theorem iSup_enorm_le_dyadic_eLpNorm_two {F : Plane → ℂ}
    (hF : Measurable F) (hF₁ : Measurable (partialFirst F))
    (hF₂ : Measurable (partialSecond F))
    (hF₂₁ : Measurable (partialSecond (partialFirst F)))
    (hC₁ : ∀ v : ℝ, ContDiff ℝ 1 (fun u => F (u, v)))
    (hC₂ : ∀ u : ℝ, ContDiff ℝ 1 (fun v => F (u, v)))
    (hC₂₁ : ∀ u : ℝ, ContDiff ℝ 1 (fun v => partialFirst F (u, v)))
    (p : ℝ≥0) (hp : 1 ≤ p) (k : ℕ) :
    (⨆ q : Plane, ‖F q‖ₑ) ≤ dyadicWeight (2 / (p : ℝ)) k *
      (eLpNorm F p volume + dyadicWeight (-1) k * eLpNorm (partialSecond F) p volume +
        dyadicWeight (-1) k * eLpNorm (partialFirst F) p volume +
        dyadicWeight (-2) k * eLpNorm (partialSecond (partialFirst F)) p volume) := by
  have hr : 0 < ((2 : ℝ) ^ (-1 : ℝ)) ^ k := by positivity
  have h := iSup_enorm_le_scaled_eLpNorm_two hF hF₁ hF₂ hF₂₁ hC₁ hC₂ hC₂₁ p hp hr
  have hw : ENNReal.ofReal (((2 : ℝ) ^ (-1 : ℝ)) ^ k) = dyadicWeight (-1) k := by
    rw [ENNReal.ofReal_pow (by positivity)]
    rfl
  rw [hw, dyadicWeight_rpow, ← ENNReal.rpow_natCast _ 2, dyadicWeight_rpow] at h
  simpa only [neg_one_mul, neg_div, neg_neg, Nat.cast_ofNat, neg_mul, one_mul] using h

theorem partialFirst_eq_fderiv {F : Plane → ℂ} {q : Plane}
    (hF : DifferentiableAt ℝ F q) : partialFirst F q = fderiv ℝ F q (1, 0) := by
  have hJ : HasDerivAt (fun u : ℝ => (u, q.2)) (1, 0) q.1 :=
    ((hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)).hasDerivAt
  exact (hF.hasFDerivAt.comp_hasDerivAt q.1 hJ).deriv

theorem partialSecond_eq_fderiv {F : Plane → ℂ} {q : Plane}
    (hF : DifferentiableAt ℝ F q) : partialSecond F q = fderiv ℝ F q (0, 1) := by
  have hJ : HasDerivAt (fun u : ℝ => (q.1, u)) (0, 1) q.2 :=
    ((hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)).hasDerivAt
  exact (hF.hasFDerivAt.comp_hasDerivAt q.2 hJ).deriv

theorem continuous_partialSecond_of_contDiff_one {F : Plane → ℂ}
    (hF : ContDiff ℝ 1 F) : Continuous (partialSecond F) := by
  have heq : partialSecond F = fun q => fderiv ℝ F q (0, 1) :=
    funext (fun q => partialSecond_eq_fderiv (hF.differentiable one_ne_zero q))
  rw [heq]
  exact (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- Joint `C²` regularity gives every regularity and measurability hypothesis
of the tensor Sobolev estimate. -/
theorem iSup_enorm_le_scaled_eLpNorm_two_of_contDiff {F : Plane → ℂ}
    (hF : ContDiff ℝ 2 F) (p : ℝ≥0) (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) :
    (⨆ q : Plane, ‖F q‖ₑ) ≤ ENNReal.ofReal r ^ (-2 / (p : ℝ)) *
      (eLpNorm F p volume + ENNReal.ofReal r * eLpNorm (partialSecond F) p volume +
        ENNReal.ofReal r * eLpNorm (partialFirst F) p volume +
        ENNReal.ofReal r ^ 2 * eLpNorm (partialSecond (partialFirst F)) p volume) := by
  have hFone : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hFD : ContDiff ℝ 1 (fderiv ℝ F) := (contDiff_succ_iff_fderiv (n := 1)).mp hF |>.2.2
  have hF₁ : ContDiff ℝ 1 (partialFirst F) := by
    have heq : partialFirst F = fun q => fderiv ℝ F q (1, 0) :=
      funext (fun q => partialFirst_eq_fderiv (hFone.differentiable one_ne_zero q))
    rw [heq]
    exact hFD.clm_apply contDiff_const
  have hF₂ : Continuous (partialSecond F) := continuous_partialSecond_of_contDiff_one hFone
  have hF₂₁ : Continuous (partialSecond (partialFirst F)) :=
    continuous_partialSecond_of_contDiff_one hF₁
  exact iSup_enorm_le_scaled_eLpNorm_two hF.continuous.measurable
    hF₁.continuous.measurable hF₂.measurable hF₂₁.measurable
    (fun v => hFone.comp (contDiff_id.prodMk (contDiff_const (c := v))))
    (fun u => hFone.comp ((contDiff_const (c := u)).prodMk contDiff_id))
    (fun u => hF₁.comp ((contDiff_const (c := u)).prodMk contDiff_id)) p hp hr

end PlanarNikodym
