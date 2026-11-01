import PlanarNikodym.Rank.AnalyticCoefficients
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

noncomputable section
open Set Filter Submodule Module
open scoped Topology
namespace PlanarNikodym

/-- The full-rank condition implies independence, including the empty family. -/
theorem independent_of_rank_eq {X : Type*} {m : ℕ} (f : Fin m → X → ℝ)
    (h : finrank ℝ (span ℝ (range f)) = m) : LinearIndependent ℝ f := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  simpa [Set.finrank] using h.symm

/-- Equal finite dimensions turn inclusion of spans into equality. -/
theorem mem_span_of_rank_eq {X : Type*} {m n : ℕ}
    (f : Fin m → X → ℝ) (g : Fin n → X → ℝ)
    (h : finrank ℝ (span ℝ (range f)) =
      finrank ℝ (span ℝ (range f) ⊔ span ℝ (range g) : Submodule ℝ (X → ℝ))) :
    ∀ i, g i ∈ span ℝ (range f) := by
  letI := FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  letI := FiniteDimensional.span_of_finite ℝ (Set.finite_range g)
  have heq := Submodule.eq_of_le_of_finrank_eq
    (show span ℝ (range f) ≤ span ℝ (range f) ⊔ span ℝ (range g) from le_sup_left) h
  intro i
  rw [heq]
  exact (show span ℝ (range g) ≤ span ℝ (range f) ⊔ span ℝ (range g) from le_sup_right) (subset_span (mem_range_self i))

/-- Lemma 5.6, simultaneously for all remaining functions. The interval is
encoded by `X`, which will be the interval subtype. Analyticity is needed only
in the parameter variable; no boundedness or t-regularity is needed. -/
theorem lemma_5_6 {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : ℕ} (f : Fin m → X → E → ℝ) (g : Fin n → X → E → ℝ)
    (W : Set E) (q : E) (hW : W ∈ 𝓝 q)
    (hf : ∀ j t, AnalyticOnNhd ℝ (f j t) W)
    (hg : ∀ i t, AnalyticOnNhd ℝ (g i t) W)
    (hrank : ∀ w ∈ W,
      finrank ℝ (span ℝ (range (fun j t => f j t w))) = m ∧
      finrank ℝ (span ℝ (range (fun j t => f j t w)) ⊔
        span ℝ (range (fun i t => g i t w)) : Submodule ℝ (X → ℝ)) = m) :
    ∃ U : Set E, IsOpen U ∧ q ∈ U ∧ U ⊆ W ∧
      ∃ C : Fin n → Fin m → E → ℝ,
        (∀ i j, AnalyticOnNhd ℝ (C i j) U) ∧
        ∀ w ∈ U, ∀ i t, g i t w = ∑ j, C i j w * f j t w := by
  classical
  have hli := independent_of_rank_eq (fun j t => f j t q) (hrank q (mem_of_mem_nhds hW)).1
  have hs : ∀ i, ∃ U : Set E, IsOpen U ∧ q ∈ U ∧ U ⊆ W ∧
      ∃ C : Fin m → E → ℝ, (∀ j, AnalyticOnNhd ℝ (C j) U) ∧
        ∀ w ∈ U, ∀ t, g i t w = ∑ j, C j w * f j t w := by
    intro i
    apply analytic_coefficients_of_mem_span f (g i) W q hW hf (hg i) hli
    intro w hw
    exact mem_span_of_rank_eq (fun j t => f j t w) (fun i t => g i t w)
      ((hrank w hw).1.trans (hrank w hw).2.symm) i
  choose U ho hq hsub C hCa hCr using hs
  obtain ⟨V, hVsub, hVopen, hqV⟩ := mem_nhds_iff.mp hW
  let S := V ∩ ⋂ i, U i
  refine ⟨S, hVopen.inter (isOpen_iInter_of_finite ho),
    ⟨hqV, mem_iInter.mpr hq⟩, fun w hw => hVsub hw.1, C, ?_, ?_⟩
  · intro i j w hw
    exact hCa i j w (mem_iInter.mp hw.2 i)
  · intro w hw i t
    exact hCr i w (mem_iInter.mp hw.2 i) t

/-- The ranks need hold only in a neighbourhood, as in (5.4). -/
theorem lemma_5_6_near {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : ℕ} (f : Fin m → X → E → ℝ) (g : Fin n → X → E → ℝ)
    (W : Set E) (q : E) (hW : IsOpen W) (hq : q ∈ W)
    (hf : ∀ j t, AnalyticOnNhd ℝ (f j t) W)
    (hg : ∀ i t, AnalyticOnNhd ℝ (g i t) W)
    (hrank : ∀ᶠ w in 𝓝 q,
      finrank ℝ (span ℝ (range (fun j t => f j t w))) = m ∧
      finrank ℝ (span ℝ (range (fun j t => f j t w)) ⊔
        span ℝ (range (fun i t => g i t w)) : Submodule ℝ (X → ℝ)) = m) :
    ∃ U : Set E, IsOpen U ∧ q ∈ U ∧ U ⊆ W ∧
      ∃ C : Fin n → Fin m → E → ℝ,
        (∀ i j, AnalyticOnNhd ℝ (C i j) U) ∧
        ∀ w ∈ U, ∀ i t, g i t w = ∑ j, C i j w * f j t w := by
  obtain ⟨V, hVsub, hVo, hqV⟩ := mem_nhds_iff.mp (inter_mem (hW.mem_nhds hq) hrank)
  obtain ⟨U, hUo, hqU, hUV, C, hCa, hCr⟩ :=
    lemma_5_6 f g V q (hVo.mem_nhds hqV)
      (fun j t w hw => hf j t w (hVsub hw).1)
      (fun i t w hw => hg i t w (hVsub hw).1)
      (fun w hw => (hVsub hw).2)
  exact ⟨U, hUo, hqU, fun w hw => (hVsub (hUV hw)).1, C, hCa, hCr⟩

/-- Paper-facing Lemma 5.6: jointly analytic functions on an interval times W.
The first m functions form the basis; n denotes the number of remaining ones.
The ambient extension is never used outside I in the rank assumptions. -/
theorem lemma_5_6_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : ℕ} (I : Set ℝ) (f : Fin m → ℝ → E → ℝ) (g : Fin n → ℝ → E → ℝ)
    (W : Set E) (q : E) (hW : IsOpen W) (hq : q ∈ W)
    (hf : ∀ j, AnalyticOnNhd ℝ (fun x : ℝ × E => f j x.1 x.2) (I ×ˢ W))
    (hg : ∀ i, AnalyticOnNhd ℝ (fun x : ℝ × E => g i x.1 x.2) (I ×ˢ W))
    (hrank : ∀ᶠ w in 𝓝 q,
      finrank ℝ (span ℝ (range (fun j (t : I) => f j t w))) = m ∧
      finrank ℝ (span ℝ (range (fun j (t : I) => f j t w)) ⊔
        span ℝ (range (fun i (t : I) => g i t w)) : Submodule ℝ (I → ℝ)) = m) :
    ∃ U : Set E, IsOpen U ∧ q ∈ U ∧ U ⊆ W ∧
      ∃ C : Fin n → Fin m → E → ℝ,
        (∀ i j, AnalyticOnNhd ℝ (C i j) U) ∧
        ∀ w ∈ U, ∀ i t, t ∈ I → g i t w = ∑ j, C i j w * f j t w := by
  have hfs : ∀ j (t : I), AnalyticOnNhd ℝ (fun w => f j t w) W := by
    intro j t w hw
    exact (hf j (t, w) ⟨t.property, hw⟩).comp (analyticAt_const.prod analyticAt_id)
  have hgs : ∀ i (t : I), AnalyticOnNhd ℝ (fun w => g i t w) W := by
    intro i t w hw
    exact (hg i (t, w) ⟨t.property, hw⟩).comp (analyticAt_const.prod analyticAt_id)
  obtain ⟨U, hUo, hqU, hUW, C, hCa, hCr⟩ := lemma_5_6_near
    (fun j (t : I) w => f j t w) (fun i (t : I) w => g i t w)
    W q hW hq hfs hgs hrank
  exact ⟨U, hUo, hqU, hUW, C, hCa, fun w hw i t ht => hCr w hw i ⟨t, ht⟩⟩

end PlanarNikodym
