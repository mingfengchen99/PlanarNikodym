import PlanarNikodym.Analysis.Fourier.GlyzChartFamilyPowerTransfer
import PlanarNikodym.Analysis.Fourier.GlyzParabolicGlobalDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzNormalizedRawExtension

/-! Actual raw-extension decoupling on one smooth time-jet chart.
The original amplitude is unchanged; the only output modification is a
compact cutoff supported in the chart. Every constant precedes the
parent scale, frequency, dyadic refinement and actual input functions. -/
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ContDiff ENNReal NNReal BigOperators
namespace PlanarNikodym

def glyzParabolicPowerCoefficient (k : ℕ) (p : ℝ≥0) (ε C Cg : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal Cg * ((2 : ℝ≥0∞) ^ (p : ℝ) * ENNReal.ofReal
    (C * (2 : ℝ) ^ (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N)) *
      (2 : ℝ≥0∞) ^ (p : ℝ))

def glyzParabolicPowerError (k W M : ℕ) (p : ℝ≥0) (ε C D L δ α : ℝ)
    (N : ℕ) (T : ℝ) (I : Finset ℕ) (g : ℕ → Plane → ℂ) : ℝ≥0∞ :=
  let e := fun i => (D * (1 + |α|) ^ (volume : Measure (GlyzConeSpace k)).integrablePower *
    (T⁻¹) ^ M) * ∫ y, ‖g i y‖
  let B : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (p : ℝ)
  let Q := ENNReal.ofReal (C * (2 : ℝ) ^
    (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N))
  (B * (Q * B * ((∑ i ∈ I, ENNReal.ofReal (e i) ^ (p : ℝ)) *
    ∫⁻ x : GlyzConeSpace k, ENNReal.ofReal (glyzNormWeight W x)) +
      ENNReal.ofReal (∑ i ∈ I, e i) ^ (p : ℝ) *
        volume (closedBall (0 : GlyzConeSpace k) 1))) *
    ENNReal.ofReal (((δ ^ k)⁻¹ * L + 1) ^ Module.finrank ℝ (GlyzConeSpace k))

def glyzRawChartExtension {d k : ℕ} (G : Family 2 d)
    (σ : Fin (k + 1) ↪ Fin (d + 2))
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (k + 1))
      ((ℝ × Aux (d + 2)) × Aux (k + 1)))
    (ρ : ((ℝ × Aux (d + 2)) × Aux (k + 1)) → ℝ)
    (a : Parameters 2 d × Plane → ℂ) (q : ℝ × Aux (d + 2))
    (r δ : ℝ) (g : Plane → ℂ) (z : Aux (k + 1)) : ℂ :=
  (ρ (q, (e (q, z)).2) : ℂ) *
    glyzRawExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a
      (glyzDenormalizedInput q.1 δ g) r
        (parameterFrame d (q.2 + coordinateInsertion σ z))

theorem Family.exists_glyz_raw_chart_parent_step {d k : ℕ} (G : Family 2 d)
    (hk : 0 < k) (hm : k + 1 ≤ d + 2) (σ : Fin (k + 1) ↪ Fin (d + 2))
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (k + 1))
      ((ℝ × Aux (d + 2)) × Aux (k + 1)))
    (he : ∀ x, e x = (x.1, G.movingLowerJetMap hm σ x))
    (hf : ∀ x ∈ e.source, ContDiffAt ℝ ∞ e x)
    (hi : ∀ x ∈ e.target, ContDiffAt ℝ ∞ e.symm x)
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a)
    (hΦ : ContDiff ℝ ∞ (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1))
    {K : Set ((ℝ × Aux (d + 2)) × Aux (k + 1))} (hK : IsCompact K) (hKT : K ⊆ e.target)
    (W M : ℕ) (hW : Module.finrank ℝ (GlyzConeSpace k) < W)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent k ≤ p)
    {ε rmin rmax : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) :
    ∃ (ρ : ((ℝ × Aux (d + 2)) × Aux (k + 1)) → ℝ)
      (C D L Cg b Cj : ℝ) (c : ℝ≥0),
      ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ (∀ z, 0 ≤ ρ z ∧ ρ z ≤ 1) ∧
      (∀ z ∈ K, ρ z = 1) ∧ tsupport ρ ⊆ e.target ∧
      0 < C ∧ 0 ≤ D ∧ 0 < L ∧ 0 < Cg ∧ 0 < b ∧ 0 < Cj ∧ 0 < c ∧
      ∀ (q : ℝ × Aux (d + 2)) (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (r : ℝ) (N : ℕ) (T : ℝ), 0 < r → 0 < T →
      1 + 2 * ((1 + |r * δ ^ (k + 1)|) * T) ≤
        (rmin / 4) * ((r * δ ^ k) / (2 * Real.pi)) * glyzDyadicScale N ^ k →
      ∀ (I : Finset ℕ) (J : ℕ → Set ℝ) (g : ℕ → Plane → ℂ),
      I ⊆ Finset.range (2 ^ N) → (∀ i, IsCompact (J i)) →
      (∀ i ∈ I, J i ⊆ Icc (0 : ℝ) 1) →
      (∀ i ∈ I, ∀ t ∈ J i, |t - glyzDyadicCenter N i| ≤ glyzDyadicScale N) →
      (∀ i, Integrable (g i)) →
      (∀ i ∈ I, Function.support (g i) ⊆ J i ×ˢ Icc rmin rmax) →
      let O := fun i => glyzRawChartExtension G σ e ρ a q r δ (g i)
      (∫⁻ z in {z | (q, z) ∈ e.source}, ‖∑ i ∈ I, O i z‖ₑ ^ (p : ℝ)) ≤
        (ENNReal.ofReal b)⁻¹ * glyzParabolicPowerCoefficient k p ε C Cg N *
          ENNReal.ofReal Cj * ∑ i ∈ I,
            (∫⁻ z in {z | (q, z) ∈ e.source}, ‖O i z‖ₑ ^ (p : ℝ)) +
        (ENNReal.ofReal b)⁻¹ *
          ((c : ℝ≥0∞) * ENNReal.ofReal |∏ i : Fin (k + 1), δ ^ (i : ℕ) / δ ^ k|)⁻¹ *
          ENNReal.ofReal δ ^ (p : ℝ) *
            glyzParabolicPowerError k W M p ε C D L δ (r * δ ^ (k + 1)) N T I g := by
  obtain ⟨ρ, A, H, hρ, hcρ, hrange, hρ1, hρT, hA, hcA, _, hH, hcH, _, hsymbol⟩ :=
    exists_glyz_raw_output_cutoff_parabolic_symbols e hi σ ha hΦ hK hKT
      (isCompact_Icc : IsCompact (Icc rmin rmax))
  have hfirst : ∀ x, (e x).1 = x.1 := by
    intro x
    simpa only using congrArg Prod.fst (he x)
  obtain ⟨b, Cj, hb, hCj, hJac⟩ :=
    exists_glyz_retained_cutoff_jacobian_bounds e hfirst hf hi ρ hcρ hρT
  obtain ⟨C, D, L, Cg, hC, hD, hL, hCg, hglobal⟩ :=
    glyz_parabolic_global_lp_L1_error d k W M hk hW A hA hcA H hH hcH hp hε hrmin
      (rmax := rmax)
  obtain ⟨c, hc, htransfer⟩ :=
    exists_glyz_chart_family_transfer_factor (glyzMomentConeCoefficientEquiv k)
  refine ⟨ρ, C, D, L, Cg, b, Cj, c, hρ, hcρ, hrange, hρ1, hρT,
    hC, hD, hL, hCg, hb, hCj, hc, ?_⟩
  intro q δ hδ hδ1 r N T hr hT hscale I J g hI hJ hJu hJc hg hgs
  let eq := retainedParameterFiber e hfirst q
  let sq : Aux (k + 1) → ℂ := fun y => (ρ (q, y) : ℂ)
  let P := fun i => glyzParabolicGlobalExtension A H q δ hδ.ne'
    (r * δ ^ (k + 1)) (r * δ ^ k) (g i)
  let O := fun i z => glyzRawExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a
    (glyzDenormalizedInput q.1 δ (g i)) r
      (parameterFrame d (q.2 + coordinateInsertion σ z))
  have hs : Function.support sq ⊆ eq.target := by
    intro y hy
    apply hρT
    apply subset_tsupport
    intro hz
    exact hy (by simp only [sq, hz, Complex.ofReal_zero])
  have hJq (z : Aux (k + 1)) (hz : z ∈ eq.source) (hn : sq (eq z) ≠ 0) :
      b ≤ |LinearMap.det (fderiv ℝ eq z).toLinearMap| ∧
        |LinearMap.det (fderiv ℝ eq z).toLinearMap| ≤ Cj := by
    apply hJac q z hz
    intro hn'
    apply hn
    change (ρ (q, (e (q, z)).2) : ℂ) = 0
    simp only [hn', Complex.ofReal_zero]
  have hrep (i : ℕ) (hiI : i ∈ I) (x : GlyzConeSpace k) :
      δ • P i x = sq ((lowerDegreeDilation k δ hδ.ne').symm (glyzMomentConeCoefficientEquiv k x)) *
        O i (eq.symm ((lowerDegreeDilation k δ hδ.ne').symm (glyzMomentConeCoefficientEquiv k x))) := by
    have hunit : Function.support (g i) ⊆ Icc (0 : ℝ) 1 ×ˢ Icc rmin rmax :=
      (hgs i hiI).trans (prod_mono (hJu i hiI) subset_rfl)
    exact G.compact_parabolic_eq_output_cutoff_denormalized hm σ e he a hΦ ρ hρT A H
      hsymbol (g i) q r hδ hδ1 hunit (glyzMomentConeCoefficientEquiv k x)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (one_le_glyzCriticalNNExponent hk).trans hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hbnd := hglobal q δ hδ hδ1 (r * δ ^ (k + 1)) N (r * δ ^ k) T
    (mul_pos hr (pow_pos hδ k)) hT hscale I J g hI hJ hJu hJc hg hgs
  exact htransfer I eq (glyz_retainedParameterFiber_smooth e hfirst hf hi q).1 sq hs
    b Cj hb hJq p δ hp0 hδ P O hrep
    (glyzParabolicPowerCoefficient k p ε C Cg N)
    (glyzParabolicPowerError k W M p ε C D L δ (r * δ ^ (k + 1)) N T I g) hbnd

end PlanarNikodym
