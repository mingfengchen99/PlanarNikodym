import PlanarNikodym.Tame.RestrictedAnalyticSets

noncomputable section
open Set

namespace PlanarNikodym

def ranZeroExtension {ι : Type*} (f : (ι → ℝ) → ℝ) (S : Set (ι → ℝ))
    (x : ι → ℝ) : ℝ := by
  classical
  exact if x ∈ S then f x else 0

theorem RanDefinableOn.zeroExtension {ι : Type*} {f : (ι → ℝ) → ℝ}
    {S : Set (ι → ℝ)} (hf : RanDefinableOn f S) (hS : RanDefinable S) :
    RanDefinableFun (ranZeroExtension f S) := by
  classical
  have hzero := (ranDefinableFun_const (ι := ι) 0).ranDefinableOn hS.compl
  change RanDefinable _ at hf hzero ⊢
  convert hf.union hzero using 1
  ext x
  by_cases hx : x ∘ some ∈ S <;> simp [Function.tupleGraph, ranZeroExtension, hx]

/-- Composition needs only coordinate graphs on the source domain; no
definability of an arbitrary extension outside that domain is required. -/
theorem RanDefinableOn.comp_on {ι κ : Type*} [Finite ι] [Finite κ]
    {f : (ι → ℝ) → ℝ} {S : Set (ι → ℝ)} (hf : RanDefinableOn f S)
    {F : (κ → ℝ) → (ι → ℝ)} {T : Set (κ → ℝ)} (hT : RanDefinable T)
    (hF : ∀ i, RanDefinableOn (fun x => F x i) T) (hm : MapsTo F T S) :
    RanDefinableOn (f ∘ F) T := by
  classical
  let E : (κ → ℝ) → (ι → ℝ) := fun x i => ranZeroExtension (fun x => F x i) T x
  have hE : RanDefinableMap E := fun i => (hF i).zeroExtension hT
  have hsub : T ⊆ E ⁻¹' S := by
    intro x hx
    have he : E x = F x := by funext i; simp only [E, ranZeroExtension, if_pos hx]
    change E x ∈ S
    rw [he]
    exact hm hx
  apply ((hf.preimage_map hE).restrict hT hsub).congr
  intro x hx
  change f (E x) = f (F x)
  congr 1
  funext i
  simp only [E, ranZeroExtension, if_pos hx]

end PlanarNikodym
