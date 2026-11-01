import PlanarNikodym.Rank.Lemma56
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Analytic.IteratedFDeriv

noncomputable section
open Set Filter Submodule Module
open scoped Topology ContDiff Matrix
namespace PlanarNikodym

/-- The derivative of a family, with values in the vector space of functions.
No norm on the function space, or uniform-in-t differentiability, is assumed. -/
def functionDerivative {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : X → E → ℝ) (p : E) : E →ₗ[ℝ] (X → ℝ) :=
  LinearMap.pi (fun t => (fderiv ℝ (f t) p).toLinearMap)

@[simp] theorem functionDerivative_apply {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : X → E → ℝ) (p v : E) (t : X) :
    functionDerivative f p v t = fderiv ℝ (f t) p v := rfl

theorem range_eq_span_coordinates {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] V) :
    L.range = span ℝ (range (fun i => L (Pi.single i 1))) := by
  have h := congrArg (Submodule.map L) (Pi.basisFun ℝ (Fin n)).span_eq
  simpa only [Submodule.map_top, ← Submodule.span_image, ← Set.range_comp,
    Function.comp_def, Pi.basisFun_apply] using h.symm

theorem functionDerivative_comp {X E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : X → F → ℝ) (g : E → F) (p : E)
    (hf : ∀ t, DifferentiableAt ℝ (f t) (g p)) (hg : DifferentiableAt ℝ g p) :
    functionDerivative (fun t x => f t (g x)) p =
      (functionDerivative f (g p)).comp (fderiv ℝ g p).toLinearMap := by
  ext v t
  exact congrArg (fun L : E →L[ℝ] ℝ => L v) (fderiv_comp p (hf t) hg)

theorem range_comp_eq_of_surjective {E F V : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup V] [Module ℝ V] (L : F →ₗ[ℝ] V) (A : E →ₗ[ℝ] F)
    (hA : Function.Surjective A) : (L.comp A).range = L.range := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨A x, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hA y
    exact ⟨x, rfl⟩

theorem isInvertible_of_det_coordinates {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (h : Matrix.det (fun i j => L (Pi.single j 1) i) ≠ 0) : L.IsInvertible := by
  let A := LinearMap.toMatrix' L.toLinearMap
  have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h)
  have hinj : Function.Injective L := by
    have hi := Matrix.mulVec_injective_iff_isUnit.mpr hA
    intro x y hxy
    apply hi
    simpa [A, LinearMap.toMatrix'_mulVec] using hxy
  have hbij : Function.Bijective L :=
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv, rfl⟩

theorem eq_zero_of_mem_span_of_eval_zero {X : Type*} {m : ℕ}
    (f : Fin m → X → ℝ) (x : Fin m → X)
    (hdet : Matrix.det (fun i j => f j (x i)) ≠ 0)
    (g : X → ℝ) (hg : g ∈ span ℝ (range f)) (hz : ∀ i, g (x i) = 0) : g = 0 := by
  classical
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℝ).mp hg
  let A : Matrix (Fin m) (Fin m) ℝ := fun i j => f j (x i)
  have hA : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet))
  have hcz : A *ᵥ c = A *ᵥ 0 := by
    ext i
    have hi := congrFun hc (x i)
    simpa [A, Matrix.mulVec, dotProduct, Finset.sum_apply, smul_eq_mul, mul_comm, hz] using hi
  have hc0 := hA hcz
  simpa [hc0] using hc.symm

/-- A local analytic inverse with explicit analytic source and target domains. -/
theorem exists_analytic_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → E) (q : E) (hf : AnalyticAt ℝ f q)
    (hi : (fderiv ℝ f q).IsInvertible) (U : Set E) (hU : U ∈ 𝓝 q) :
    ∃ e : OpenPartialHomeomorph E E, q ∈ e.source ∧ e.source ⊆ U ∧
      (∀ x, e x = f x) ∧ AnalyticOnNhd ℝ e e.source ∧
      AnalyticOnNhd ℝ e.symm e.target := by
  obtain ⟨L, hL⟩ := hi
  have hd : HasFDerivAt f (L : E →L[ℝ] E) q := hL ▸ hf.differentiableAt.hasFDerivAt
  have hc : ContDiffAt ℝ ω f q := hf.contDiffAt
  let e₀ := hc.toOpenPartialHomeomorph f hd (by simp)
  have hq : q ∈ e₀.source := hc.mem_toOpenPartialHomeomorph_source hd (by simp)
  have he : ∀ x, e₀ x = f x := fun _ => rfl
  have hinv : AnalyticAt ℝ e₀.symm (e₀ q) := by
    exact (hc.to_localInverse hd (by simp)).analyticAt
  have hgood : ∀ᶠ x in 𝓝 q, x ∈ U ∧ AnalyticAt ℝ f x ∧ AnalyticAt ℝ e₀.symm (e₀ x) := by
    have hp := (e₀.continuousAt hq).preimage_mem_nhds hinv.eventually_analyticAt
    filter_upwards [hU, hf.eventually_analyticAt, hp] with x hx ha hb
    exact ⟨hx, ha, hb⟩
  obtain ⟨S, hS, hSo, hqS⟩ := mem_nhds_iff.mp hgood
  refine ⟨e₀.restr S, ?_, ?_, fun _ => rfl, ?_, ?_⟩
  · rw [e₀.restr_source' S hSo]
    exact ⟨hq, hqS⟩
  · intro x hx
    exact (hS ((e₀.restr_source' S hSo) ▸ hx).2).1
  · intro x hx
    exact (hS ((e₀.restr_source' S hSo) ▸ hx).2).2.1
  · intro y hy
    have hx := (e₀.restr S).map_target hy
    have hxy := (e₀.restr S).right_inv hy
    have ha := (hS ((e₀.restr_source' S hSo) ▸ hx).2).2.2
    have hxy₀ : e₀ (e₀.symm y) = y := by
      simpa only [OpenPartialHomeomorph.restr_apply,
        OpenPartialHomeomorph.restr_symm_apply] using hxy
    change AnalyticAt ℝ e₀.symm y
    simpa only [OpenPartialHomeomorph.restr_symm_apply, hxy₀] using ha

end PlanarNikodym
