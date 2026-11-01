import PlanarNikodym.Geometry.AnalyticCylindricalPartition
import PlanarNikodym.Geometry.NonzeroDirectionFrame

/-! Concrete parametrized analytic strata. The constructors below produce
open connected bounded parameter domains, analytic immersions and an actual
continuous inverse on the image; these properties are proved for the
constructed maps rather than supplied as decomposition input. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

structure AnalyticStratificationChart (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  dim : ℕ
  source : Set (Fin dim → ℝ)
  open_source : IsOpen source
  bounded_source : Bornology.IsBounded source
  connected_source : IsConnected source
  map : (Fin dim → ℝ) → E
  inverse : E → (Fin dim → ℝ)
  analytic_map : AnalyticOnNhd ℝ map source
  continuous_inverse : ContinuousOn inverse (map '' source)
  left_inverse : ∀ x ∈ source, inverse (map x) = x
  derivative_injective : ∀ x ∈ source, Function.Injective (fderiv ℝ map x)

namespace AnalyticStratificationChart
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def image (Q : AnalyticStratificationChart E) : Set E := Q.map '' Q.source

theorem map_injOn (Q : AnalyticStratificationChart E) : InjOn Q.map Q.source := by
  intro x hx y hy he
  simpa only [Q.left_inverse x hx, Q.left_inverse y hy] using congrArg Q.inverse he

theorem connected_image (Q : AnalyticStratificationChart E) : IsConnected Q.image :=
  Q.connected_source.image Q.map Q.analytic_map.continuousOn

theorem fderiv_injective_of_factor {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {U : Set S} (hU : IsOpen U) {x : S} (hx : x ∈ U)
    (f : S → F) (g : S → E) (I : F → E)
    (hf : DifferentiableAt ℝ f x) (hI : DifferentiableAt ℝ I (f x))
    (he : EqOn (I ∘ f) g U) (hi : Function.Injective (fderiv ℝ g x)) :
    Function.Injective (fderiv ℝ f x) := by
  have hevent : I ∘ f =ᶠ[𝓝 x] g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact he hy
  have hd : (fderiv ℝ I (f x)).comp (fderiv ℝ f x) = fderiv ℝ g x := by
    rw [← fderiv_comp x hI hf]
    exact hevent.fderiv_eq
  intro v w hvw
  apply hi
  rw [← hd]
  exact congrArg (fderiv ℝ I (f x)) hvw

def postcompose (Q : AnalyticStratificationChart E) (f : E → F) (I : F → E)
    (hf : AnalyticOnNhd ℝ f Q.image)
    (hI : AnalyticOnNhd ℝ I (f '' Q.image))
    (hleft : ∀ y ∈ Q.image, I (f y) = y) : AnalyticStratificationChart F where
  dim := Q.dim
  source := Q.source
  open_source := Q.open_source
  bounded_source := Q.bounded_source
  connected_source := Q.connected_source
  map := f ∘ Q.map
  inverse := Q.inverse ∘ I
  analytic_map := fun x hx => (hf (Q.map x) (mem_image_of_mem _ hx)).comp (Q.analytic_map x hx)
  continuous_inverse := by
    apply Q.continuous_inverse.comp
    · exact hI.continuousOn.mono (by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨Q.map x, mem_image_of_mem _ hx, rfl⟩)
    · rintro _ ⟨x, hx, rfl⟩
      change I (f (Q.map x)) ∈ Q.map '' Q.source
      rw [hleft _ (mem_image_of_mem _ hx)]
      exact mem_image_of_mem _ hx
  left_inverse := by
    intro x hx
    dsimp only [Function.comp_apply]
    rw [hleft _ (mem_image_of_mem _ hx), Q.left_inverse x hx]
  derivative_injective := by
    intro x hx
    apply fderiv_injective_of_factor Q.open_source hx (f ∘ Q.map) Q.map I
    · exact ((hf _ (mem_image_of_mem _ hx)).comp (Q.analytic_map x hx)).differentiableAt
    · exact (hI _ ⟨Q.map x, mem_image_of_mem _ hx, rfl⟩).differentiableAt
    · intro y hy
      exact hleft _ (mem_image_of_mem _ hy)
    · exact Q.derivative_injective x hx

@[simp] theorem postcompose_image (Q : AnalyticStratificationChart E) (f : E → F) (I : F → E)
    (hf : AnalyticOnNhd ℝ f Q.image) (hI : AnalyticOnNhd ℝ I (f '' Q.image))
    (hleft : ∀ y ∈ Q.image, I (f y) = y) :
    (Q.postcompose f I hf hI hleft).image = f '' Q.image := by
  exact Set.image_comp f Q.map Q.source

def graph (Q : AnalyticStratificationChart E) (ρ : E → ℝ)
    (hρ : AnalyticOnNhd ℝ ρ Q.image) : AnalyticStratificationChart (E × ℝ) :=
  Q.postcompose (analyticGraphMap ρ) Prod.fst
    (fun x hx => analyticAt_id.prod (hρ x hx))
    (fun _ _ => analyticAt_fst) (fun _ _ => rfl)

@[simp] theorem graph_dim (Q : AnalyticStratificationChart E) (ρ : E → ℝ)
    (hρ : AnalyticOnNhd ℝ ρ Q.image) : (Q.graph ρ hρ).dim = Q.dim := rfl

@[simp] theorem graph_image (Q : AnalyticStratificationChart E) (ρ : E → ℝ)
    (hρ : AnalyticOnNhd ℝ ρ Q.image) :
    (Q.graph ρ hρ).image = analyticGraph Q.image ρ := by
  rw [graph, postcompose_image, analyticGraphMap_image]

end AnalyticStratificationChart
end PlanarNikodym
