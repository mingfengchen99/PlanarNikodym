import PlanarNikodym.Analysis.Fourier.GlyzDyadicWhitney
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Actual finite-exponent Lp bounds for the Whitney expansion. These
lemmas use the original Schwartz pieces and their actual block sums. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace PlanarNikodym
set_option maxHeartbeats 800000

theorem glyz_holder_half (p : ℝ≥0) (hp : 0 < p) :
    ENNReal.HolderTriple (p : ℝ≥0∞) p ((p / 2 : ℝ≥0) : ℝ≥0∞) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have ht : Real.HolderTriple (p : ℝ) p ((p : ℝ) / 2) :=
    ⟨by field_simp; norm_num, hpR, hpR⟩
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_ofNat, ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat] using ht.ennrealOfReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def glyzBilinearLp (p : ℝ≥0) (f g : SchwartzMap E ℂ) : ℝ :=
  lpNorm (fun x => f x * star (g x)) (p / 2 : ℝ≥0) volume

theorem memLp_glyz_pair (p : ℝ≥0) (hp : 0 < p) (f g : SchwartzMap E ℂ) :
    MemLp (fun x => f x * star (g x)) (p / 2 : ℝ≥0) volume := by
  letI : ENNReal.HolderTriple (p : ℝ≥0∞) p ((p / 2 : ℝ≥0) : ℝ≥0∞) := glyz_holder_half p hp
  exact ((g.memLp (p : ℝ≥0∞) volume).star).mul' (r := ((p / 2 : ℝ≥0) : ℝ≥0∞)) (f.memLp (p : ℝ≥0∞) volume)

theorem glyzBilinearLp_le (p : ℝ≥0) (hp : 0 < p) (f g : SchwartzMap E ℂ) :
    glyzBilinearLp p f g ≤ lpNorm (f : E → ℂ) p volume * lpNorm (g : E → ℂ) p volume := by
  letI : ENNReal.HolderTriple (p : ℝ≥0∞) p ((p / 2 : ℝ≥0) : ℝ≥0∞) := glyz_holder_half p hp
  have h := eLpNorm_smul_le_mul_eLpNorm (p := (p : ℝ≥0∞)) (q := p)
    (r := ((p / 2 : ℝ≥0) : ℝ≥0∞))
    ((g.memLp (p : ℝ≥0∞) volume).star.aestronglyMeasurable) (f.memLp (p : ℝ≥0∞) volume).aestronglyMeasurable
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top (f.memLp (p : ℝ≥0∞) volume).eLpNorm_ne_top
    ((g.memLp (p : ℝ≥0∞) volume).star).eLpNorm_ne_top) h
  rw [ENNReal.toReal_mul, eLpNorm_star] at hh
  change (eLpNorm (fun x => f x * star (g x)) (p / 2 : ℝ≥0) volume).toReal ≤
    (eLpNorm (f : E → ℂ) p volume).toReal * (eLpNorm (g : E → ℂ) p volume).toReal at hh
  simpa only [glyzBilinearLp,
    toReal_eLpNorm (memLp_glyz_pair p hp f g).aestronglyMeasurable,
    toReal_eLpNorm (f.memLp (p : ℝ≥0∞) volume).aestronglyMeasurable,
    toReal_eLpNorm (g.memLp (p : ℝ≥0∞) volume).aestronglyMeasurable] using hh

theorem glyzBilinearLp_self (p : ℝ≥0) (hp : 0 < p) (f : SchwartzMap E ℂ) :
    glyzBilinearLp p f f = lpNorm (f : E → ℂ) p volume ^ (2 : ℕ) := by
  have hm : (((p / 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal 2) = p := by
    norm_cast
    exact div_mul_cancel₀ p (by norm_num)
  have he : eLpNorm (fun x => f x * star (f x)) (p / 2 : ℝ≥0) volume =
      eLpNorm (f : E → ℂ) p volume ^ (2 : ℕ) := by
    calc
      _ = eLpNorm (fun x => ‖f x‖ ^ (2 : ℝ)) (p / 2 : ℝ≥0) volume :=
        eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => by
          simp only [norm_mul, norm_star, Real.rpow_two, Real.norm_eq_abs,
            abs_of_nonneg (norm_nonneg _), pow_two])
      _ = _ := by rw [eLpNorm_norm_rpow _ (by norm_num : (0 : ℝ) < 2), hm, ENNReal.rpow_two]
  unfold glyzBilinearLp
  rw [← toReal_eLpNorm (memLp_glyz_pair p hp f f).aestronglyMeasurable, he,
    ENNReal.toReal_pow, toReal_eLpNorm (f.memLp (p : ℝ≥0∞) volume).aestronglyMeasurable]

theorem glyzBilinearLp_le_sq_add_sq (p : ℝ≥0) (hp : 0 < p) (f g : SchwartzMap E ℂ) :
    glyzBilinearLp p f g ≤ lpNorm (f : E → ℂ) p volume ^ (2 : ℕ) +
      lpNorm (g : E → ℂ) p volume ^ (2 : ℕ) := by
  apply (glyzBilinearLp_le p hp f g).trans
  nlinarith [sq_nonneg (lpNorm (f : E → ℂ) p volume - lpNorm (g : E → ℂ) p volume),
    sq_nonneg (lpNorm (f : E → ℂ) p volume), sq_nonneg (lpNorm (g : E → ℂ) p volume)]

end PlanarNikodym
