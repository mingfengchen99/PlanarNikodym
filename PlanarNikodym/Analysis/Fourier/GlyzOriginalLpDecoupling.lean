import PlanarNikodym.Analysis.Fourier.GlyzOriginalEpsilonPower
import PlanarNikodym.Analysis.Fourier.GlyzLpL2Error
import PlanarNikodym.Analysis.Fourier.DecouplingExponents

/-! The original cinematic extension satisfies the sharp Lp estimate
with its original amplitude and a compact-frequency L2 error. This
module is the sharp dyadic version; smooth partitions are handled by
the fixed translated-grid construction. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace PlanarNikodym

theorem glyz_power_exponent_eq_lp_exponent {k : ℕ} (hk : 0 < k)
    {p : ℝ} (hp : 0 < p) (ε : ℝ) :
    (p - glyzCriticalExponent k / 2 - 1) / k + p * ε =
      p * (coneDecouplingExponent k p + ε) := by
  have hkR : (k : ℝ) ≠ 0 := by positivity
  unfold glyzCriticalExponent coneDecouplingExponent
  field_simp
  ring

theorem Family.exists_glyz_original_lp_decoupling {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ K)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε rmin rmax Q : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (r : ℝ),
      (2 : ℝ) ^ N ≤ r → r ≤ (2 : ℝ) ^ (N + 1) →
      ∀ g : Plane → ℂ, MemLp g 2 →
      Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1} →
      Function.support g ⊆ {y | y.2 ∈ Icc rmin rmax} →
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      let F := glyzVariableFinalDepth (d + 1) N
      lpNorm (glyzRawExtension Φ a g r) p volume ≤
        C * r ^ (coneDecouplingExponent (d + 1) p + ε) *
          (∑ i ∈ Finset.range (2 ^ F),
            lpNorm (glyzRawExtension Φ a (glyzDyadicInput F i g) r) p volume ^
              (p : ℝ)) ^ (1 / (p : ℝ)) +
        C * r ^ (-Q) * lpNorm g 2 volume := by
  have hp1 : 1 ≤ p := (one_le_glyzCriticalNNExponent (by omega : 0 < d + 1)).trans hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  obtain ⟨C, hC, hpower⟩ := G.exists_glyz_original_epsilon_power hG ha hc hK hdet has hp
    (mul_pos hp0 hε) hrmin (mul_nonneg p.coe_nonneg hQ) (rmax := rmax)
  let J : Set Plane := Icc (0 : ℝ) 1 ×ˢ Icc rmin rmax
  have hJ : volume J ≠ ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  let B : ℝ := C ^ (1 / (p : ℝ)) * max 1 (Real.sqrt (volume J).toReal)
  have hB : 0 < B := mul_pos (Real.rpow_pos_of_pos hC _) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨B, hB, fun N r hr hr' g hg hgt hgr => ?_⟩
  let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
  let F := glyzVariableFinalDepth (d + 1) N
  have hgs : Function.support g ⊆ J := fun y hy =>
    ⟨⟨(hgt hy).1, (hgt hy).2.le⟩, hgr hy⟩
  have hgi := integrable_of_memLp_two_support_finite hg hJ hgs
  have hΦ : ContDiff ℝ ∞ Φ := hG.comp (contDiff_snd.prodMk contDiff_fst)
  have hraw := memLp_glyzRawExtension volume hΦ ha hc hgi r p
  have hpieces (i : ℕ) (_ : i ∈ Finset.range (2 ^ F)) :
      MemLp (glyzRawExtension Φ a (glyzDyadicInput F i g) r) p :=
    memLp_glyzRawExtension volume hΦ ha hc (integrable_glyzDyadicInput hgi F i) r p
  have hh := hpower N r hr hr' g hgi hgt hgr
  dsimp only at hh
  have hexp := glyz_power_exponent_eq_lp_exponent (by omega : 0 < d + 1) hp0 ε
  simp only [Nat.cast_add, Nat.cast_one] at hexp
  rw [hexp,
    show -((p : ℝ) * Q) = -(p : ℝ) * Q by ring] at hh
  exact glyz_lp_L2_of_power_bound volume (Finset.range (2 ^ F))
    (glyzRawExtension Φ a g r)
    (fun i => glyzRawExtension Φ a (glyzDyadicInput F i g) r)
    hp1 hraw hpieces hg hJ hgs hC.le
    (lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 ^ N) hr) hh

end PlanarNikodym
