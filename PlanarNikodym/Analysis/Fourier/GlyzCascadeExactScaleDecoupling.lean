import PlanarNikodym.Analysis.Fourier.GlyzCascadeExactScalePower
import PlanarNikodym.Analysis.Fourier.GlyzLpL1Error
import PlanarNikodym.Analysis.Fourier.GlyzOriginalLpDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzExactScaleBudget

/-! Successive degree decoupling at the exact scale r^(-1/2). The right side uses the actual standard smooth time slices of
the original amplitude, and the final error is the original L1 mass. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace PlanarNikodym

/-- Exact-scale decoupling of the original globally smooth phase. The
constant is chosen before the frequency and input, and no analytic
estimate is assumed. The arbitrarily decaying error retains the actual
L1 input mass without requiring compact input support. -/
theorem Family.exists_glyz_cascade_exact_scale_decoupling_L1 {d : ℕ} (G : Family 2 d)
    (hd : 1 ≤ d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ K)
    (hKt : ∀ x ∈ K, x.1 ∈ Ioo (-1 : ℝ) 1)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε rmin rmax Q : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      ∀ g : Plane → ℂ, Integrable g →
      Function.support g ⊆ {y | y.2 ∈ Icc rmin rmax} →
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      let δ := r ^ (-(1 / (2 : ℝ)))
      lpNorm (glyzRawExtension Φ a g r) p volume ≤
        C * r ^ ((1 / 2 - (d + 1 : ℝ) / p) + ε) *
          (∑ i : Fin (glyzExactTimeCount δ),
            lpNorm (timeSliceExtension Φ a g r (-1 + (i : ℝ) * δ) δ) p volume ^
              (p : ℝ)) ^ (1 / (p : ℝ)) +
        C * r ^ (-Q) * (∫ y, ‖g y‖) := by
  have hp1 : 1 ≤ p := (one_le_glyzCriticalNNExponent (by omega : 0 < d + 1)).trans hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  obtain ⟨C, hC, hpower⟩ := G.exists_glyz_cascade_exact_scale_power hd hG ha hc hK hdet has hKt hp
    (mul_pos hp0 hε) hrmin (mul_nonneg p.coe_nonneg hQ) (rmax := rmax)
  let B : ℝ := C ^ (1 / (p : ℝ))
  have hB : 0 < B := Real.rpow_pos_of_pos hC _
  refine ⟨B, hB, fun r hr g hgi hgr => ?_⟩
  let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
  let δ := r ^ (-(1 / (2 : ℝ)))
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hδ : 0 < δ := Real.rpow_pos_of_pos hr0 _
  have hΦ : ContDiff ℝ ∞ Φ := hG.comp (contDiff_snd.prodMk contDiff_fst)
  have hraw := memLp_glyzRawExtension volume hΦ ha hc hgi r p
  have hpieces (i : Fin (glyzExactTimeCount δ)) (_ : i ∈ Finset.univ) :
      MemLp (glyzRawExtension Φ a (glyzExactTimePiece δ i g) r) p :=
    memLp_glyzRawExtension volume hΦ ha hc (integrable_glyzExactTimePiece hgi δ i) r p
  have hh := hpower r hr g hgi hgr
  dsimp only at hh
  have hexp : (p : ℝ) / 2 - (d + 1) + (p : ℝ) * ε =
      (p : ℝ) * ((1 / 2 - (d + 1 : ℝ) / p) + ε) := by
    field_simp [hp0.ne']
  rw [hexp, show -((p : ℝ) * Q) = -(p : ℝ) * Q by ring] at hh
  have hnorm := glyz_lp_L1_of_power_bound volume Finset.univ
    (glyzRawExtension Φ a g r)
    (fun i : Fin (glyzExactTimeCount δ) =>
      glyzRawExtension Φ a (glyzExactTimePiece δ i g) r)
    hp1 hraw hpieces hgi hC.le hr0 hh
  simpa only [glyzRawExtension_exactTimePiece_eq_timeSliceExtension Φ a g r hδ] using hnorm

end PlanarNikodym
