import PlanarNikodym.Projection.FactorialLinearControl
import PlanarNikodym.Projection.CompactTaylorControl
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open Set Filter Finset MeasureTheory
open scoped Topology Nat ENNReal
namespace PlanarNikodym.Wisewell

/-- The actual bounded factorial graph admits arbitrarily small covers
after a scalar `C¹` map whose second coordinate derivative never vanishes.
The cancellation slope must lie strictly inside the coefficient bound. -/
theorem exists_factorial_prefix_cover (M : ℝ) (hM : 0 ≤ M) (f : Plane → ℝ)
    (hf : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-M) M, DifferentiableAt ℝ f p)
    (hDf : ContinuousOn (fderiv ℝ f) (Icc (0 : ℝ) 1 ×ˢ Icc (-M) M))
    (hβ : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-M) M, fderiv ℝ f p (0, 1) ≠ 0)
    (hslope : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-M) M,
      |fderiv ℝ f p (1, 0) / fderiv ℝ f p (0, 1)| < M)
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ a : FactorialDigits,
      ‖f (factorialPoint (boundedCoefficientSchedule M) a) -
        f (prefixFactorialPoint (boundedCoefficientSchedule M) N (factorialPrefix N a))‖ ≤
          (max 1 M + 2) * η / ((N + 1)! : ℝ) := by
  let R : Set Plane := Icc (0 : ℝ) 1 ×ˢ Icc (-M) M
  let r := boundedCoefficientSchedule M
  let C := max 1 M
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hr : ∀ n p, ‖r n p‖ ≤ M := boundedCoefficientSchedule_norm_le M hM
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hRc : Convex ℝ R := (convex_Icc (0 : ℝ) 1).prod (convex_Icc (-M) M)
  obtain ⟨δ, hδ, hTaylor⟩ := exists_uniform_affine_remainder f R hR hRc hf hDf η hη
  obtain ⟨B₀, hB₀⟩ := hR.exists_bound_of_continuousOn hDf
  let B := max 1 B₀
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbound : ∀ p ∈ R, ‖fderiv ℝ f p‖ ≤ B :=
    fun p hp => (hB₀ p hp).trans (le_max_right _ _)
  have hshift : Tendsto (fun k : ℕ => k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_right k 1) tendsto_id
  have hfact : Tendsto (fun k : ℕ => ((k + 1)! : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (factorial_tendsto_atTop.comp hshift)
  have hsmall : ∀ᶠ k : ℕ in atTop, C / ((k + 1)! : ℝ) < δ :=
    (tendsto_const_nhds.div_atTop hfact).eventually (gt_mem_nhds hδ)
  have hnat : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have htail : ∀ᶠ k : ℕ in atTop, B * C / ((k : ℝ) + 2) < η :=
    (tendsto_const_nhds.div_atTop hnat).eventually (gt_mem_nhds hη)
  obtain ⟨k, hkδ, hkη⟩ := (hsmall.and htail).exists
  let z : FactorialPrefix k → Plane := prefixFactorialPoint r k
  have hz : ∀ p, z p ∈ R := fun p =>
    factorialPoint_mem_rectangle r M hM hr (factorialPrefixExtend k p)
  let s : FactorialPrefix k → ℝ := fun p =>
    -(fderiv ℝ f (z p) (1, 0) / fderiv ℝ f (z p) (0, 1))
  have hs : ∀ p, |s p| < M := fun p => by
    simpa only [s, abs_neg] using hslope (z p) (hz p)
  obtain ⟨N, hkN, hN⟩ := boundedCoefficientSchedule_approximates M k s hs
    (η / B) (div_pos hη hB)
  refine ⟨N, ?_⟩
  intro a
  let x := factorialPoint r a
  let xN := prefixFactorialPoint r N (factorialPrefix N a)
  let z₀ := z (factorialPrefix k a)
  let A := fderiv ℝ f z₀
  have hx : x ∈ R := factorialPoint_mem_rectangle r M hM hr a
  have hxN : xN ∈ R := factorialPoint_mem_rectangle r M hM hr
    (factorialPrefixExtend N (factorialPrefix N a))
  have hz₀ : z₀ ∈ R := hz _
  have hxz : ‖x - z₀‖ < δ :=
    (norm_factorialPoint_sub_prefix_le r M hM hr a k).trans_lt hkδ
  have hxNz : ‖xN - z₀‖ < δ :=
    (norm_prefixFactorialPoint_sub_earlier_le r M hM hr a k N hkN).trans_lt hkδ
  have hT := hTaylor xN hxN x hx z₀ hz₀ hxNz hxz
  have hA : ‖A‖ ≤ B := hbound z₀ hz₀
  have hAb : ‖A (0, 1)‖ ≤ B := by
    calc
      ‖A (0, 1)‖ ≤ ‖A‖ * ‖((0, 1) : Plane)‖ := A.le_opNorm _
      _ = ‖A‖ := by simp
      _ ≤ B := hA
  have hecoef : A (1, 0) + A (0, 1) * r N (factorialPrefix N a) =
      -A (0, 1) * (s (factorialPrefix k a) - r N (factorialPrefix N a)) := by
    have hb : A (0, 1) ≠ 0 := hβ z₀ hz₀
    change A (1, 0) + A (0, 1) * r N (factorialPrefix N a) =
      -A (0, 1) * (-(A (1, 0) / A (0, 1)) - r N (factorialPrefix N a))
    field_simp [hb]
    ring
  have hcoef : ‖A (1, 0) + A (0, 1) * r N (factorialPrefix N a)‖ ≤ η := by
    rw [hecoef, norm_mul, norm_neg, Real.norm_eq_abs (s _ - _)]
    calc
      ‖A (0, 1)‖ * |s (factorialPrefix k a) - r N (factorialPrefix N a)| ≤
          B * (η / B) := mul_le_mul hAb (le_of_lt (hN a)) (abs_nonneg _) (le_of_lt hB)
      _ = η := by field_simp
  have hlin := norm_linear_factorialPoint_tail_le r M hM hr a N A η (le_of_lt hη) hcoef
  have hden : 0 < ((N + 1)! : ℝ) := by positivity
  have hNt : B * C / ((N : ℝ) + 2) ≤ η := by
    apply le_trans _ (le_of_lt hkη)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast Nat.add_le_add_right hkN 2
  have hfac : ((N + 2)! : ℝ) = ((N : ℝ) + 2) * ((N + 1)! : ℝ) := by
    rw [show N + 2 = (N + 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hlast : ‖A‖ * C / ((N + 2)! : ℝ) ≤ η / ((N + 1)! : ℝ) := by
    calc
      ‖A‖ * C / ((N + 2)! : ℝ) ≤ B * C / ((N + 2)! : ℝ) := by
        gcongr
      _ = (B * C / ((N : ℝ) + 2)) / ((N + 1)! : ℝ) := by
        rw [hfac, div_mul_eq_div_div]
      _ ≤ η / ((N + 1)! : ℝ) := div_le_div_of_nonneg_right hNt (le_of_lt hden)
  have hrem : ‖f x - f xN - A (x - xN)‖ ≤ η * C / ((N + 1)! : ℝ) := by
    apply hT.trans
    have hpoint := norm_factorialPoint_sub_prefix_le r M hM hr a N
    calc
      η * ‖x - xN‖ ≤ η * (C / ((N + 1)! : ℝ)) :=
        mul_le_mul_of_nonneg_left hpoint (le_of_lt hη)
      _ = _ := by ring
  change ‖f x - f xN‖ ≤ _
  calc
    ‖f x - f xN‖ ≤ ‖f x - f xN - A (x - xN)‖ + ‖A (x - xN)‖ := by
      calc
        ‖f x - f xN‖ = ‖(f x - f xN - A (x - xN)) + A (x - xN)‖ := by
          congr 1
          ring
        _ ≤ _ := norm_add_le _ _
    _ ≤ η * C / ((N + 1)! : ℝ) +
        (η / ((N + 1)! : ℝ) + η / ((N + 1)! : ℝ)) :=
      add_le_add hrem (hlin.trans (add_le_add_right hlast _))
    _ = _ := by dsimp [C]; ring

/-- The factorial graph constructed above has a genuinely null scalar
image. No null-set or selector-existence hypothesis is used. -/
theorem volume_image_boundedFactorialGraph_eq_zero (M : ℝ) (hM : 0 ≤ M) (f : Plane → ℝ)
    (hf : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-M) M, DifferentiableAt ℝ f p)
    (hDf : ContinuousOn (fderiv ℝ f) (Icc (0 : ℝ) 1 ×ˢ Icc (-M) M))
    (hβ : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-M) M, fderiv ℝ f p (0, 1) ≠ 0)
    (hslope : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-M) M,
      |fderiv ℝ f p (1, 0) / fderiv ℝ f p (0, 1)| < M) :
    volume (f '' boundedFactorialGraph M) = 0 := by
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let K := max 1 M + 2
  have hK : 0 < K := by dsimp [K]; have := le_max_left (1 : ℝ) M; linarith
  let η : ℝ := (ε : ℝ) / (2 * K)
  have hη : 0 < η := div_pos (by exact_mod_cast hε) (by positivity)
  obtain ⟨N, hN⟩ := exists_factorial_prefix_cover M hM f hf hDf hβ hslope η hη
  let ρ := K * η / ((N + 1)! : ℝ)
  let center : FactorialPrefix N → ℝ := fun p =>
    f (prefixFactorialPoint (boundedCoefficientSchedule M) N p)
  have hcover : f '' boundedFactorialGraph M ⊆
      ⋃ p : FactorialPrefix N, Metric.closedBall (center p) ρ := by
    rintro _ ⟨_, ⟨a, _, rfl⟩, rfl⟩
    apply mem_iUnion.mpr
    refine ⟨factorialPrefix N a, ?_⟩
    simpa only [Metric.mem_closedBall, dist_eq_norm, factorialPoint, center, ρ, K] using hN a
  have hmeasure : volume (f '' boundedFactorialGraph M) ≤
      ENNReal.ofReal (2 * K * η) := by
    calc
      volume (f '' boundedFactorialGraph M) ≤
          volume (⋃ p : FactorialPrefix N, Metric.closedBall (center p) ρ) := measure_mono hcover
      _ ≤ ∑ p : FactorialPrefix N, volume (Metric.closedBall (center p) ρ) :=
        measure_iUnion_fintype_le _ _
      _ = (Fintype.card (FactorialPrefix N) : ℝ≥0∞) * ENNReal.ofReal (2 * ρ) := by
        simp only [Real.volume_closedBall, sum_const, card_univ, nsmul_eq_mul]
      _ = ENNReal.ofReal (2 * K * η) := by
        rw [card_factorialPrefix, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [ρ]
        field_simp
  have hηeq : 2 * K * η = (ε : ℝ) := by dsimp [η]; field_simp
  simpa only [hηeq, ENNReal.ofReal_coe_nnreal, zero_add] using hmeasure

end PlanarNikodym.Wisewell
