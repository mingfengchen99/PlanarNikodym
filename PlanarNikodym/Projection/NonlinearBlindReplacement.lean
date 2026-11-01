import PlanarNikodym.Core.Definitions
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-! A quantitative, nonlinear segment replacement lemma.

The proof uses directional derivatives and the intermediate value theorem.
It is the local covering step of the Venetian-blind construction; the growth
factor tends to one as the directions approach one another.
-/

noncomputable section
open Set
open scoped Topology

namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A centered segment; `a` is the parameter half-length. -/
def centeredBlindSegment (c v : E) (a : ℝ) : Set E :=
  (fun t : ℝ => c + t • v) '' Icc (-a) a

theorem isCompact_centeredBlindSegment (c v : E) (a : ℝ) :
    IsCompact (centeredBlindSegment c v a) :=
  isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))

theorem mem_centeredBlindSegment (c v : E) {a t : ℝ} (ht : |t| ≤ a) :
    c + t • v ∈ centeredBlindSegment c v a :=
  ⟨t, abs_le.mp ht, rfl⟩

/-- An ordered mean-value inequality in an arbitrary real normed space. -/
theorem image_le_of_fderiv_direction_nonneg
    {f : E → ℝ} {S : Set E} {x y : E}
    (hS : Convex ℝ S) (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hx : x ∈ S) (hy : y ∈ S)
    (hd : ∀ z ∈ S, 0 ≤ fderiv ℝ f z (y - x)) :
    f x ≤ f y := by
  let g : ℝ → E := fun t => x + t • (y - x)
  have hgmem : ∀ t ∈ Icc (0 : ℝ) 1, g t ∈ S := by
    intro t ht
    exact hS.add_smul_sub_mem hx hy ht
  have hg : ∀ t, HasDerivAt g (y - x) t := by
    intro t
    simpa [g] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hfg : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t => f (g t)) (fderiv ℝ f (g t) (y - x)) t := by
    intro t ht
    exact (hf _ (hgmem t ht)).hasFDerivAt.comp_hasDerivAt t (hg t)
  have hmono : MonotoneOn (fun t => f (g t)) (Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun t ht => (hfg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hfg t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by rw [(hfg t (interior_subset ht)).deriv]; exact hd _ (hgmem t (interior_subset ht)))
  simpa [g] using hmono (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one) zero_le_one

/-- Linear algebra behind a small rotation: expansion compensates for the
error in direction, uniformly over the entire old segment. -/
theorem blind_endpoint_direction_nonneg
    (A : E →L[ℝ] ℝ) {v w : E} {a s m M η Λ : ℝ}
    (ha : 0 ≤ a) (hs : |s| ≤ a) (hm : 0 < m) (hM : 0 ≤ M)
    (hη : 0 ≤ η) (hΛ : 1 + M / m * η ≤ Λ)
    (hAw : m ≤ A w) (hAnorm : ‖A‖ ≤ M) (hvw : ‖w - v‖ ≤ η) :
    0 ≤ A ((Λ * a) • w - s • v) ∧
      0 ≤ A (s • v - (-Λ * a) • w) := by
  have hΛone : 1 ≤ Λ := by
    have : 0 ≤ M / m * η := by positivity
    linarith
  have hΛm : M * η ≤ (Λ - 1) * m := by
    have := (div_le_iff₀ hm).mp (show M * η / m ≤ Λ - 1 by
      calc
        M * η / m = M / m * η := by ring
        _ ≤ Λ - 1 := by linarith)
    nlinarith
  have herr : |A (w - v)| ≤ M * η := by
    calc
      |A (w - v)| = ‖A (w - v)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖A‖ * ‖w - v‖ := A.le_opNorm _
      _ ≤ M * η := mul_le_mul hAnorm hvw (norm_nonneg _) hM
  have hsa := abs_le.mp hs
  have he : |s * A (w - v)| ≤ a * (M * η) := by
    rw [abs_mul]
    exact mul_le_mul hs herr (abs_nonneg _) ha
  have he' := abs_le.mp he
  simp only [map_sub] at he'
  have hcoef₁ : 0 ≤ Λ * a - s := by nlinarith
  have hcoef₂ : 0 ≤ Λ * a + s := by nlinarith
  have hbound₁ := mul_le_mul_of_nonneg_left hAw hcoef₁
  have hbound₂ := mul_le_mul_of_nonneg_left hAw hcoef₂
  have hbudget := mul_le_mul_of_nonneg_left hΛm ha
  have hrewrite₁ : (Λ * a) • w - s • v = (Λ * a - s) • w + s • (w - v) := by
    module
  have hrewrite₂ : s • v - (-Λ * a) • w = (Λ * a + s) • w - s • (w - v) := by
    module
  simp only [hrewrite₁, hrewrite₂, map_add, map_sub, map_smul]
  simp only [smul_eq_mul]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hsa.2) hm.le,
    mul_nonneg (by linarith : 0 ≤ a + s) hm.le]

/-- A small change of direction preserves the entire nonlinear projection,
at the cost of the factor `1 + (M/m)η` in parameter length. -/
theorem image_centeredBlindSegment_subset_of_direction_change
    {f : E → ℝ} {S : Set E} {c v w : E} {a m M η Λ : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hΛ : 1 + M / m * η ≤ Λ) (hvw : ‖w - v‖ ≤ η)
    (hS : Convex ℝ S) (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hd : ∀ z ∈ S, m ≤ fderiv ℝ f z w)
    (hbound : ∀ z ∈ S, ‖fderiv ℝ f z‖ ≤ M)
    (hvS : centeredBlindSegment c v a ⊆ S)
    (hwS : centeredBlindSegment c w (Λ * a) ⊆ S) :
    f '' centeredBlindSegment c v a ⊆
      f '' centeredBlindSegment c w (Λ * a) := by
  rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  have hΛone : 1 ≤ Λ := by
    have : 0 ≤ M / m * η := by positivity
    linarith
  have hb : 0 ≤ Λ * a := mul_nonneg (by linarith) ha
  have hold : c + s • v ∈ S := hvS ⟨s, hs, rfl⟩
  have hlo : c + (-Λ * a) • w ∈ S := by
    apply hwS
    apply mem_centeredBlindSegment
    rw [show -Λ * a = -(Λ * a) by ring, abs_neg, abs_of_nonneg hb]
  have hhi : c + (Λ * a) • w ∈ S := hwS (mem_centeredBlindSegment _ _ (by rw [abs_of_nonneg hb]))
  have hlow : f (c + (-Λ * a) • w) ≤ f (c + s • v) := by
    apply image_le_of_fderiv_direction_nonneg hS hf hlo hold
    intro z hz
    have hh := (blind_endpoint_direction_nonneg (fderiv ℝ f z)
      ha (abs_le.mpr hs) hm hM hη hΛ (hd z hz) (hbound z hz) hvw).2
    convert hh using 1
    congr 1
    abel
  have hupp : f (c + s • v) ≤ f (c + (Λ * a) • w) := by
    apply image_le_of_fderiv_direction_nonneg hS hf hold hhi
    intro z hz
    have hh := (blind_endpoint_direction_nonneg (fderiv ℝ f z)
      ha (abs_le.mpr hs) hm hM hη hΛ (hd z hz) (hbound z hz) hvw).1
    convert hh using 1
    congr 1
    abel
  have hcont : ContinuousOn (fun t : ℝ => f (c + t • w)) (Icc (-(Λ*a)) (Λ*a)) := by
    have hfc : ContinuousOn f S := fun z hz => (hf z hz).continuousAt.continuousWithinAt
    exact hfc.comp
      (show Continuous (fun t : ℝ => c + t • w) from
        continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      (fun t ht => hwS ⟨t, ht, rfl⟩)
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc (by linarith : -(Λ*a) ≤ Λ*a)
    hcont (show f (c + s • v) ∈ Icc (f (c + (-(Λ*a)) • w))
      (f (c + (Λ*a) • w)) by exact ⟨by simpa only [neg_mul] using hlow, hupp⟩)
  exact ⟨c + t • w, ⟨t, ht, rfl⟩, heq⟩

/-- Initial covering: a sufficiently long transverse segment captures
the projection of every nearby point, for the actual nonlinear map. -/
theorem mem_image_centeredBlindSegment_of_near_center
    {f : E → ℝ} {S : Set E} {c w q : E} {a m M : ℝ}
    (ha : 0 ≤ a)
    (hS : Convex ℝ S) (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hd : ∀ z ∈ S, m ≤ fderiv ℝ f z w)
    (hbound : ∀ z ∈ S, ‖fderiv ℝ f z‖ ≤ M)
    (hq : q ∈ S) (hseg : centeredBlindSegment c w a ⊆ S)
    (hnear : M * ‖q - c‖ ≤ m * a) :
    f q ∈ f '' centeredBlindSegment c w a := by
  have hlo : c + (-a) • w ∈ S :=
    hseg (mem_centeredBlindSegment _ _ (by rw [abs_neg, abs_of_nonneg ha]))
  have hhi : c + a • w ∈ S :=
    hseg (mem_centeredBlindSegment _ _ (by rw [abs_of_nonneg ha]))
  have he (z : E) (hz : z ∈ S) :
      |fderiv ℝ f z (q - c)| ≤ m * a := by
    calc
      |fderiv ℝ f z (q - c)| = ‖fderiv ℝ f z (q - c)‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ f z‖ * ‖q - c‖ := (fderiv ℝ f z).le_opNorm _
      _ ≤ M * ‖q - c‖ := mul_le_mul_of_nonneg_right (hbound z hz) (norm_nonneg _)
      _ ≤ m * a := hnear
  have hlow : f (c + (-a) • w) ≤ f q := by
    apply image_le_of_fderiv_direction_nonneg hS hf hlo hq
    intro z hz
    have hid : q - (c + (-a) • w) = (q - c) + a • w := by module
    rw [hid, map_add, map_smul, smul_eq_mul]
    have ha' := mul_le_mul_of_nonneg_left (hd z hz) ha
    linarith [(abs_le.mp (he z hz)).1]
  have hupp : f q ≤ f (c + a • w) := by
    apply image_le_of_fderiv_direction_nonneg hS hf hq hhi
    intro z hz
    have hid : c + a • w - q = a • w - (q - c) := by module
    rw [hid, map_sub, map_smul, smul_eq_mul]
    have ha' := mul_le_mul_of_nonneg_left (hd z hz) ha
    linarith [(abs_le.mp (he z hz)).2]
  have hcont : ContinuousOn (fun t : ℝ => f (c + t • w)) (Icc (-a) a) := by
    have hfc : ContinuousOn f S := fun z hz => (hf z hz).continuousAt.continuousWithinAt
    exact hfc.comp
      (show Continuous (fun t : ℝ => c + t • w) from
        continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      (fun t ht => hseg ⟨t, ht, rfl⟩)
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc (by linarith : -a ≤ a) hcont ⟨hlow, hupp⟩
  exact ⟨c + t • w, ⟨t, ht, rfl⟩, heq⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Reversing the sign of a scalar map does not alter an image-inclusion
claim. This lets each centre parameter choose its own derivative orientation. -/
theorem scalar_image_subset_of_mul_image_subset
    {f : E → ℝ} {A B : Set E} {σ : ℝ} (hσ : σ ≠ 0)
    (h : (fun q => σ * f q) '' A ⊆ (fun q => σ * f q) '' B) :
    f '' A ⊆ f '' B := by
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨p, hp, he⟩ := h ⟨q, hq, rfl⟩
  exact ⟨p, hp, mul_left_cancel₀ hσ he⟩

end PlanarNikodym
