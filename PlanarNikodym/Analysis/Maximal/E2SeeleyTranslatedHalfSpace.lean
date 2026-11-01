import PlanarNikodym.Analysis.Maximal.E2SeeleyCompactHalfSpace

/-! Actual translated and reversed half-space extension. -/
noncomputable section
open Set
open scoped ContDiff
namespace PlanarNikodym
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem e2_exists_extension_of_halfspace_chart (e : (ℝ × E) ≃ₜ (ℝ × E))
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {s : Set (ℝ × E)} (hs : e ⁻¹' s = e2PositiveHalfSpace E)
    {f : (ℝ × E) → F} (hf : ContDiffOn ℝ ∞ f s) (hc : HasCompactSupport f) :
    ∃ g : (ℝ × E) → F, ContDiff ℝ ∞ g ∧ EqOn g f s := by
  have hfe : ContDiffOn ℝ ∞ (f ∘ e) (e2PositiveHalfSpace E) :=
    hf.comp he.contDiffOn (by intro x hx; change x ∈ e ⁻¹' s; rwa [hs])
  refine ⟨e2SeeleyExtension (f ∘ e) ∘ e.symm,
    (e2SeeleyExtension_contDiff_of_compact_contDiffOn hfe (hc.comp_homeomorph e)).comp hi, ?_⟩
  intro x hx
  have hxs : e.symm x ∈ e2PositiveHalfSpace E := by
    rw [← hs]
    simpa using hx
  simp only [Function.comp_apply, e2SeeleyExtension_eq hxs, e.apply_symm_apply]

def e2LeftTimeChart (a : ℝ) : (ℝ × E) ≃ₜ (ℝ × E) :=
  (Homeomorph.addLeft a).prodCongr (Homeomorph.refl E)

def e2RightTimeChart (b : ℝ) : (ℝ × E) ≃ₜ (ℝ × E) :=
  ((Homeomorph.neg ℝ).trans (Homeomorph.addLeft b)).prodCongr (Homeomorph.refl E)

omit [NormedSpace ℝ E] in
@[simp] theorem e2LeftTimeChart_apply (a : ℝ) (x : ℝ × E) :
    e2LeftTimeChart a x = (a + x.1, x.2) := rfl
omit [NormedSpace ℝ E] in
@[simp] theorem e2LeftTimeChart_symm_apply (a : ℝ) (x : ℝ × E) :
    (e2LeftTimeChart (E := E) a).symm x = (-a + x.1, x.2) := rfl
omit [NormedSpace ℝ E] in
@[simp] theorem e2RightTimeChart_apply (b : ℝ) (x : ℝ × E) :
    e2RightTimeChart b x = (b + -x.1, x.2) := rfl
omit [NormedSpace ℝ E] in
@[simp] theorem e2RightTimeChart_symm_apply (b : ℝ) (x : ℝ × E) :
    (e2RightTimeChart (E := E) b).symm x = (-(-b + x.1), x.2) := rfl

theorem e2_exists_extension_left_halfspace (a : ℝ)
    {f : (ℝ × E) → F} (hf : ContDiffOn ℝ ∞ f (Ici a ×ˢ univ))
    (hc : HasCompactSupport f) :
    ∃ g : (ℝ × E) → F, ContDiff ℝ ∞ g ∧ EqOn g f (Ici a ×ˢ univ) := by
  apply e2_exists_extension_of_halfspace_chart (e2LeftTimeChart a)
    ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)
    ((contDiff_const.add contDiff_fst).prodMk contDiff_snd) _ hf hc
  ext x
  simp only [mem_preimage, mem_prod, e2LeftTimeChart_apply, mem_Ici, mem_univ, and_true,
    e2PositiveHalfSpace]
  constructor <;> intro h <;> linarith

theorem e2_exists_extension_right_halfspace (b : ℝ)
    {f : (ℝ × E) → F} (hf : ContDiffOn ℝ ∞ f (Iic b ×ˢ univ))
    (hc : HasCompactSupport f) :
    ∃ g : (ℝ × E) → F, ContDiff ℝ ∞ g ∧ EqOn g f (Iic b ×ˢ univ) := by
  apply e2_exists_extension_of_halfspace_chart (e2RightTimeChart b)
    ((contDiff_const.add contDiff_fst.neg).prodMk contDiff_snd)
    ((contDiff_const.add contDiff_fst).neg.prodMk contDiff_snd) _ hf hc
  ext x
  simp only [mem_preimage, mem_prod, e2RightTimeChart_apply, mem_Iic, mem_Ici, mem_univ, and_true,
    e2PositiveHalfSpace]
  constructor <;> intro h <;> linarith

end PlanarNikodym
