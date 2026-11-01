import PlanarNikodym.Geometry.AnalyticFiniteFiberZeros
import Mathlib.Data.Set.Card.Arithmetic

/-! A common finite-fiber neighborhood for a finite analytic family.
The neighborhoods and the bound are constructed before the neighboring
parameter is quantified. The finite index type may be empty. -/

noncomputable section
open Set Filter
open scoped Topology

namespace PlanarNikodym

/-- A finite family of actual nonflat analytic vertical germs has a common
product neighborhood and a uniform finite bound for the union of all its
vertical zero fibers. This does not assert analytic root branches or
separating sign partitions. -/
theorem exists_uniform_finite_analytic_family_fiber_zeros
    {J E : Type*} [Finite J]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : J → E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ)
    (hf : ∀ j, AnalyticAt ℝ (f j) (x₀, t₀))
    (hnf : ∀ j, ¬ ∀ᶠ t in 𝓝 t₀, f j (x₀, t) = 0) :
    ∃ (U : Set E) (V : Set ℝ) (N : ℕ),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧
      ∀ x ∈ U, {t : ℝ | t ∈ V ∧ ∃ j, f j (x, t) = 0}.Finite ∧
        {t : ℝ | t ∈ V ∧ ∃ j, f j (x, t) = 0}.ncard ≤ N := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  choose m U V hU hxU hV htV hzeros using
    fun j => exists_uniform_finite_analytic_fiber_zeros_of_nonflat
      (f j) x₀ t₀ (hf j) (hnf j)
  let U₀ : Set E := ⋂ j, U j
  let V₀ : Set ℝ := ⋂ j, V j
  refine ⟨U₀, V₀, ∑ j, m j, isOpen_iInter_of_finite hU,
    mem_iInter.mpr hxU, isOpen_iInter_of_finite hV, mem_iInter.mpr htV, ?_⟩
  intro x hx
  let Z : J → Set ℝ := fun j => {t | t ∈ V j ∧ f j (x, t) = 0}
  have hZ (j : J) : (Z j).Finite ∧ (Z j).ncard ≤ m j :=
    hzeros j x (mem_iInter.mp hx j)
  have hfin : (⋃ j, Z j).Finite := finite_iUnion (fun j => (hZ j).1)
  have hsub : {t : ℝ | t ∈ V₀ ∧ ∃ j, f j (x, t) = 0} ⊆ ⋃ j, Z j := by
    rintro t ⟨ht, j, hj⟩
    exact mem_iUnion.mpr ⟨j, mem_iInter.mp ht j, hj⟩
  refine ⟨hfin.subset hsub, ?_⟩
  exact (ncard_le_ncard hsub hfin).trans
    ((ncard_iUnion_le_of_fintype Z).trans
      (Finset.sum_le_sum fun j _ => (hZ j).2))

end PlanarNikodym
