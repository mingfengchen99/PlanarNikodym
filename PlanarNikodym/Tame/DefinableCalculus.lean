import PlanarNikodym.Tame.DefinableTopology
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Definability of genuine directional derivatives, obtained by spelling
out punctured limits in the ordered real field. No derivative symbol is
added to the restricted analytic language. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology

namespace PlanarNikodym

theorem ranDefinableFun_abs {ι : Type*} {f : (ι → ℝ) → ℝ}
    (hf : RanDefinableFun f) : RanDefinableFun (fun x => |f x|) := by
  classical
  convert hf.ite (ranDefinable_le (ranDefinableFun_const 0) hf)
    (ranDefinableFun_neg hf) using 1
  funext x
  split_ifs with hx
  · exact abs_of_nonneg hx
  · exact abs_of_neg (lt_of_not_ge hx)

theorem ranDefinableFun_inv {ι : Type*} [Finite ι] {f : (ι → ℝ) → ℝ}
    (hf : RanDefinableFun f) : RanDefinableFun (fun x => (f x)⁻¹) := by
  have hbase : RanDefinableFun (fun w : Option ι → ℝ => f (w ∘ some)) :=
    hf.comp (fun i => ranDefinableFun_coordinate (some i))
  have hzero := (hbase.setOf_eq (ranDefinableFun_const 0)).inter
    ((ranDefinableFun_coordinate none).setOf_eq (ranDefinableFun_const 0))
  have hone := (ranDefinableFun_mul hbase (ranDefinableFun_coordinate none)).setOf_eq
    (ranDefinableFun_const 1)
  change RanDefinable _
  convert hzero.union hone using 1
  ext w
  change (f (w ∘ some))⁻¹ = w none ↔
    (f (w ∘ some) = 0 ∧ w none = 0) ∨ f (w ∘ some) * w none = 1
  by_cases hx : f (w ∘ some) = 0
  · simp [hx, eq_comm]
  · simp only [hx, false_and, false_or]
    constructor
    · intro h
      rw [← h, mul_inv_cancel₀ hx]
    · intro h
      calc
        (f (w ∘ some))⁻¹ = (f (w ∘ some))⁻¹ * 1 := (mul_one _).symm
        _ = (f (w ∘ some))⁻¹ * (f (w ∘ some) * w none) := by rw [h]
        _ = w none := by rw [← mul_assoc, inv_mul_cancel₀ hx, one_mul]

theorem ranDefinable_eventually_nhdsNE_zero {ι : Type*} [Finite ι]
    {P : (ι → ℝ) → ℝ → Prop}
    (hP : RanDefinable {w : Option ι → ℝ | P (w ∘ some) (w none)}) :
    RanDefinable {x | ∀ᶠ t in 𝓝[≠] (0 : ℝ), P x t} := by
  have hpull := hP.preimage_comp (fun | none => none | some i => some (some i))
  have hsmall : RanDefinable {w : Option (Option ι) → ℝ |
      w none ≠ 0 ∧ |w none| < w (some none)} :=
    ((ranDefinableFun_coordinate none).setOf_eq (ranDefinableFun_const 0)).compl.inter
      (ranDefinable_lt (ranDefinableFun_abs (ranDefinableFun_coordinate none))
        (ranDefinableFun_coordinate (some none)))
  have hall := ranDefinable_forall_real
    (P := fun w t => (t ≠ 0 ∧ |t| < w none) → P (w ∘ some) t)
    (hsmall.himp hpull)
  have hpos : RanDefinable {w : Option ι → ℝ | 0 < w none} :=
    ranDefinable_lt (ranDefinableFun_const 0) (ranDefinableFun_coordinate none)
  have hex := ranDefinable_exists_real
    (P := fun x δ => 0 < δ ∧ ∀ t, (t ≠ 0 ∧ |t| < δ) → P x t)
    (hpos.inter hall)
  convert hex using 1
  ext x
  change {t | P x t} ∈ 𝓝[≠] (0 : ℝ) ↔ _
  rw [Metric.mem_nhdsWithin_iff]
  simp only [subset_def, mem_inter_iff, mem_ball, Real.dist_eq, sub_zero,
    mem_compl_iff, mem_singleton_iff]
  exact exists_congr fun δ => and_congr_right fun _ =>
    forall_congr' fun t => by tauto

/-- Parameterized punctured limits of definable functions form a definable
relation. The limit value may itself be a free coordinate. -/
theorem ranDefinable_tendsto_nhdsNE_zero {ι : Type*} [Finite ι]
    {F : (Option ι → ℝ) → ℝ} {g : (ι → ℝ) → ℝ}
    (hF : RanDefinableFun F) (hg : RanDefinableFun g) :
    RanDefinable {x | Tendsto (fun t => F (fun i => Option.elim i t x))
      (𝓝[≠] (0 : ℝ)) (𝓝 (g x))} := by
  have harg : RanDefinableMap
      (fun w : Option (Option ι) → ℝ => fun i => Option.elim i (w none)
        (fun j => w (some (some j)))) := by
    intro i
    cases i with
    | none => exact ranDefinableFun_coordinate none
    | some j => exact ranDefinableFun_coordinate (some (some j))
  have hval := hF.comp harg
  have hlim := hg.comp (fun i => ranDefinableFun_coordinate (some (some i)))
  have hclose := ranDefinable_lt (ranDefinableFun_abs (ranDefinableFun_sub hval hlim))
    (ranDefinableFun_coordinate (some none))
  have hev := ranDefinable_eventually_nhdsNE_zero
    (P := fun w t => |F (fun i => Option.elim i t (w ∘ some)) - g (w ∘ some)| < w none)
    hclose
  have hpos : RanDefinable {w : Option ι → ℝ | 0 < w none} :=
    ranDefinable_lt (ranDefinableFun_const 0) (ranDefinableFun_coordinate none)
  have hall := ranDefinable_forall_real
    (P := fun x ε => 0 < ε → ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      |F (fun i => Option.elim i t x) - g x| < ε) (hpos.himp hev)
  convert hall using 1
  ext x
  simp only [mem_setOf_eq, Metric.tendsto_nhds, Real.dist_eq]

/-- A fixed directional derivative is definable wherever the original
function is differentiable. This statement uses the actual `fderiv`. -/
theorem RanDefinableFun.directionalDerivativeOn {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} (hf : RanDefinableFun f)
    {S : Set (ι → ℝ)} (hS : RanDefinable S)
    (hd : ∀ x ∈ S, DifferentiableAt ℝ f x) (v : ι → ℝ) :
    RanDefinableOn (fun x => fderiv ℝ f x v) S := by
  have hshift : RanDefinableMap (fun w : Option (Option ι) → ℝ =>
      fun i => w (some (some i)) + w none * v i) := fun i =>
    ranDefinableFun_add (ranDefinableFun_coordinate (some (some i)))
      (ranDefinableFun_mul (ranDefinableFun_coordinate none) (ranDefinableFun_const (v i)))
  have hbase := hf.comp (fun i => ranDefinableFun_coordinate (some (some i)))
  have hslope := ranDefinableFun_mul
    (ranDefinableFun_inv (ranDefinableFun_coordinate (ι := Option (Option ι)) none))
    (ranDefinableFun_sub (hf.comp hshift) hbase)
  have hlimit := ranDefinable_tendsto_nhdsNE_zero hslope
    (ranDefinableFun_coordinate (ι := Option ι) none)
  unfold RanDefinableOn
  convert (hS.preimage_comp some).inter hlimit using 1
  ext w
  apply and_congr_right
  intro hx
  have hline : HasDerivAt (fun t : ℝ => (w ∘ some) + t • v) v 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    convert (hasDerivAt_const (0 : ℝ) (w (some i))).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (v i)) using 1 <;> simp
    funext t
    rfl
  have hdf : HasFDerivAt f (fderiv ℝ f (w ∘ some)) ((w ∘ some) + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using (hd _ hx).hasFDerivAt
  have hder := hdf.comp_hasDerivAt 0 hline
  have ht := hder.tendsto_slope_zero
  simp only [Function.comp_apply, zero_add, zero_smul, add_zero, smul_eq_mul] at ht
  change fderiv ℝ f (w ∘ some) v = w none ↔
    Tendsto (fun t : ℝ => t⁻¹ * (f ((w ∘ some) + t • v) - f (w ∘ some)))
      (𝓝[≠] 0) (𝓝 (w none))
  constructor
  · intro he
    simpa only [← he] using ht
  · intro h
    exact tendsto_nhds_unique ht h

/-- Domain-local version: an arbitrary extension of `f` outside `S`
does not enter the conclusion. -/
theorem RanDefinableOn.directionalDerivative {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} {S : Set (ι → ℝ)}
    (hf : RanDefinableOn f S) (hS : RanDefinable S) (ho : IsOpen S)
    (hd : ∀ x ∈ S, DifferentiableAt ℝ f x) (v : ι → ℝ) :
    RanDefinableOn (fun x => fderiv ℝ f x v) S := by
  have he (x : ι → ℝ) (hx : x ∈ S) : ranZeroExtension f S =ᶠ[𝓝 x] f := by
    filter_upwards [ho.mem_nhds hx] with y hy
    simp only [ranZeroExtension, if_pos hy]
  have hdext (x : ι → ℝ) (hx : x ∈ S) :
      DifferentiableAt ℝ (ranZeroExtension f S) x :=
    (he x hx).differentiableAt_iff.mpr (hd x hx)
  apply ((hf.zeroExtension hS).directionalDerivativeOn hS hdext v).congr
  intro x hx
  exact congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L v) ((he x hx).fderiv_eq (𝕜 := ℝ))

end PlanarNikodym
