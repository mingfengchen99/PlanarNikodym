import PlanarNikodym.Analysis.Maximal.E2FIOFullKernel
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The full T*T energy identity, with actual compact-support
integrability and Fubini proofs. No short-time partition is used. -/
noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
namespace PlanarNikodym
variable {Q : Type*} [NormedAddCommGroup Q]
  [MeasurableSpace Q] [BorelSpace Q]

theorem e2_gram_triple_integrable (μ : Measure Q) [SFinite μ]
    [IsFiniteMeasureOnCompacts μ] {F : Q × Plane → ℂ}
    (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun z : Q × (Plane × Plane) => conj (F (z.1, z.2.1)) * F (z.1, z.2.2))
      (μ.prod (volume.prod volume)) := by
  have hct : HasCompactSupport
      (fun z : Q × (Plane × Plane) => conj (F (z.1, z.2.1)) * F (z.1, z.2.2)) := by
    apply HasCompactSupport.intro
      ((hc.isCompact.image continuous_fst).prod
        ((hc.isCompact.image continuous_snd).prod (hc.isCompact.image continuous_snd)))
    intro z hz
    by_cases h1 : F (z.1, z.2.1) = 0
    · simp [h1]
    by_cases h2 : F (z.1, z.2.2) = 0
    · simp [h2]
    exfalso
    apply hz
    have hs1 : (z.1, z.2.1) ∈ tsupport F := subset_tsupport F h1
    have hs2 : (z.1, z.2.2) ∈ tsupport F := subset_tsupport F h2
    exact ⟨⟨_, hs1, rfl⟩, ⟨⟨_, hs1, rfl⟩, ⟨_, hs2, rfl⟩⟩⟩
  exact ((Complex.continuous_conj.comp (hF.comp (continuous_fst.prodMk continuous_snd.fst))).mul
    (hF.comp (continuous_fst.prodMk continuous_snd.snd))).integrable_of_hasCompactSupport hct

theorem e2_full_gram_energy (μ : Measure Q) [SFinite μ]
    [IsFiniteMeasureOnCompacts μ] {F : Q × Plane → ℂ}
    (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun q => ‖∫ x : Plane, F (q, x)‖ ^ (2 : ℕ)) μ ∧
      (∫ q, ‖∫ x : Plane, F (q, x)‖ ^ (2 : ℕ) ∂μ) =
        (∫ x : Plane, ∫ y : Plane, ∫ q, conj (F (q, x)) * F (q, y) ∂μ).re := by
  let G := fun q : Q => ∫ z : Plane × Plane, conj (F (q, z.1)) * F (q, z.2) ∂volume.prod volume
  have htri := e2_gram_triple_integrable μ hF hc
  have hG : Integrable G μ := htri.integral_prod_left
  have he (q : Q) : G q = (‖∫ x : Plane, F (q, x)‖ ^ (2 : ℕ) : ℝ) := by
    rw [show G q = (∫ x : Plane, conj (F (q, x))) * ∫ y : Plane, F (q, y) from
      integral_prod_mul (μ := volume) (ν := volume) (fun x : Plane => conj (F (q, x))) (fun y : Plane => F (q, y)), integral_conj, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have hre (q : Q) : RCLike.re (G q) = ‖∫ x : Plane, F (q, x)‖ ^ (2 : ℕ) := by
    change (G q).re = _
    rw [he q, Complex.ofReal_re]
  have hreal : Integrable (fun q => ‖∫ x : Plane, F (q, x)‖ ^ (2 : ℕ)) μ :=
    hG.re.congr (Filter.Eventually.of_forall hre)
  refine ⟨hreal, ?_⟩
  have hswap := integral_integral_swap (μ := μ) (ν := volume.prod volume)
    (f := fun q (z : Plane × Plane) => conj (F (q, z.1)) * F (q, z.2)) htri
  have hp := integral_prod (fun z : Plane × Plane => ∫ q, conj (F (q, z.1)) * F (q, z.2) ∂μ)
    htri.integral_prod_right
  have hg : (∫ q, G q ∂μ) = ∫ x : Plane, ∫ y : Plane, ∫ q, conj (F (q, x)) * F (q, y) ∂μ :=
    hswap.trans hp
  have hrr : (∫ q, G q ∂μ).re = ∫ q, ‖∫ x : Plane, F (q, x)‖ ^ (2 : ℕ) ∂μ := by
    calc
      _ = ∫ q, RCLike.re (G q) ∂μ := (integral_re hG).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall hre)
  exact hrr.symm.trans (congrArg Complex.re hg)

theorem e2FullFIOIntegral_gram_energy (μ : Measure Q) [SFinite μ]
    [IsFiniteMeasureOnCompacts μ] (r : ℝ) (Φ : Q → Plane → ℝ)
    (a : Q × Plane → ℂ) (f : Plane → ℂ)
    (hK : Continuous (Function.uncurry (e2FIOAmplitudeKernel r Φ a)))
    (hc : HasCompactSupport (Function.uncurry (e2FIOAmplitudeKernel r Φ a)))
    (hf : Continuous f) :
    Integrable (fun q => ‖e2FullFIOIntegral r Φ a f q‖ ^ (2 : ℕ)) μ ∧
      (∫ q, ‖e2FullFIOIntegral r Φ a f q‖ ^ (2 : ℕ) ∂μ) =
        (∫ x : Plane, ∫ y : Plane, (conj (f x) * f y) * e2FIOGramKernel μ r Φ a x y).re := by
  have hh := e2_full_gram_energy μ (hK.mul (hf.comp continuous_snd)) hc.mul_right
  refine ⟨hh.1, hh.2.trans ?_⟩
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with y
  change (∫ q, conj (e2FIOAmplitudeKernel r Φ a q x * f x) *
    (e2FIOAmplitudeKernel r Φ a q y * f y) ∂μ) = _
  calc
    _ = ∫ q, (conj (f x) * f y) *
        (conj (e2FIOAmplitudeKernel r Φ a q x) * e2FIOAmplitudeKernel r Φ a q y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with q
      rw [map_mul]
      ring
    _ = _ := integral_const_mul _ _


theorem e2FullFIOIntegral_gram_energy_of_continuous_amplitude
    (μ : Measure Q) [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    (r : ℝ) (Φ : Q → Plane → ℝ) (a : Q × Plane → ℂ) (f : Plane → ℂ)
    (hΦ : Continuous (Function.uncurry Φ)) (ha : Continuous a)
    (hc : HasCompactSupport a) (hf : Continuous f) :
    Integrable (fun q => ‖e2FullFIOIntegral r Φ a f q‖ ^ (2 : ℕ)) μ ∧
      (∫ q, ‖e2FullFIOIntegral r Φ a f q‖ ^ (2 : ℕ) ∂μ) =
        (∫ x : Plane, ∫ y : Plane, (conj (f x) * f y) * e2FIOGramKernel μ r Φ a x y).re := by
  have hK : Continuous (Function.uncurry (e2FIOAmplitudeKernel r Φ a)) :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul hΦ)).mul continuous_const)).mul ha
  have hKc : HasCompactSupport (Function.uncurry (e2FIOAmplitudeKernel r Φ a)) := by
    apply HasCompactSupport.intro hc.isCompact
    intro z hz
    change Complex.exp _ * a z = 0
    rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  exact e2FullFIOIntegral_gram_energy μ r Φ a f hK hKc hf

end PlanarNikodym
