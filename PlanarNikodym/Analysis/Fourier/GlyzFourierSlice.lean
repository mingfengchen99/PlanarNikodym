import PlanarNikodym.Analysis.Fourier.GlyzMomentBoxRescaling
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Fourier.Inversion

/-! Actual Fourier marginal representation and Fourier support of every
affine orthogonal slice. Integrability and Fubini are proved; no slicing
support hypothesis or lower-degree gain is postulated. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory FourierTransform Real
open scoped FourierTransform RealInnerProductSpace
namespace PlanarNikodym
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def glyzFourierMarginal (F : WithLp 2 (H × V) → ℂ) (z : V) (ξ : H) : ℂ :=
  ∫ η : V, 𝐞 (inner ℝ η z) • F (WithLp.toLp 2 (ξ, η))

theorem glyz_integrable_char_smul {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] {μ : Measure X} {F : X → ℂ} (hF : Integrable F μ)
    (φ : X → ℝ) (hφ : Continuous φ) : Integrable (fun x => 𝐞 (φ x) • F x) μ := by
  apply hF.norm.mono' ((continuous_fourierChar.comp hφ).aestronglyMeasurable.smul hF.aestronglyMeasurable)
  filter_upwards [] with x
  simp

theorem integrable_glyzFourierMarginal {F : WithLp 2 (H × V) → ℂ} (hF : Integrable F)
    (z : V) : Integrable (glyzFourierMarginal F z) := by
  have hp : Integrable (fun q : H × V => F (WithLp.toLp 2 q)) (volume.prod volume) :=
    (WithLp.volume_preserving_toLp H V).integrable_comp_of_integrable hF
  have hc := glyz_integrable_char_smul hp (fun q : H × V => inner ℝ q.2 z) (by fun_prop)
  exact hc.integral_prod_left

theorem fourierInv_glyzFourierMarginal {F : WithLp 2 (H × V) → ℂ} (hF : Integrable F)
    (z : V) (x : H) :
    𝓕⁻ (glyzFourierMarginal F z) x = 𝓕⁻ F (WithLp.toLp 2 (x, z)) := by
  have hp : Integrable (fun q : H × V => F (WithLp.toLp 2 q)) (volume.prod volume) :=
    (WithLp.volume_preserving_toLp H V).integrable_comp_of_integrable hF
  have hc := glyz_integrable_char_smul hp
    (fun q : H × V => inner ℝ q.1 x + inner ℝ q.2 z) (by fun_prop)
  rw [fourierInv_eq, fourierInv_eq]
  have he : (∫ q : H × V, 𝐞 (inner ℝ q.1 x + inner ℝ q.2 z) • F (WithLp.toLp 2 q)
      ∂volume.prod volume) =
      ∫ q : WithLp 2 (H × V), 𝐞 (inner ℝ q (WithLp.toLp 2 (x, z))) • F q := by
    exact (WithLp.volume_preserving_toLp H V).integral_comp
      (MeasurableEquiv.toLp 2 (H × V)).measurableEmbedding
      (fun q : WithLp 2 (H × V) => 𝐞 (inner ℝ q (WithLp.toLp 2 (x, z))) • F q)
  rw [← he, integral_prod _ hc]
  apply integral_congr_ae
  filter_upwards [] with ξ
  unfold glyzFourierMarginal
  simp_rw [Circle.smul_def]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with η
  rw [AddChar.map_add_eq_mul, Circle.coe_mul, mul_smul]

end PlanarNikodym

namespace PlanarNikodym
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem glyzSliceEmbedding_isometry (z : V) :
    Isometry (fun x : H => WithLp.toLp 2 (x, z)) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  change ‖WithLp.toLp 2 (x - y, z - z)‖ = ‖x - y‖
  rw [sub_self, WithLp.norm_toLp_fst]

def glyzSliceSchwartz (f : SchwartzMap (WithLp 2 (H × V)) ℂ) (z : V) : SchwartzMap H ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (show (fun x : H => WithLp.toLp 2 (x, z)).HasTemperateGrowth from by
      change (fun x : H => (WithLp.prodContinuousLinearEquiv 2 ℝ H V).symm (x, z)).HasTemperateGrowth
      exact (WithLp.prodContinuousLinearEquiv 2 ℝ H V).symm.toContinuousLinearMap.hasTemperateGrowth.comp
        (by
          have hh : (fun x : H => (ContinuousLinearMap.inl ℝ H V) x + (0, z)).HasTemperateGrowth := by fun_prop
          simpa using hh)) (glyzSliceEmbedding_isometry z).antilipschitz f

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem glyzSliceSchwartz_apply (f : SchwartzMap (WithLp 2 (H × V)) ℂ)
    (z : V) (x : H) : glyzSliceSchwartz f z x = f (WithLp.toLp 2 (x, z)) := rfl

theorem fourierInv_glyzFourierMarginal_fourier (f : SchwartzMap (WithLp 2 (H × V)) ℂ)
    (z : V) : 𝓕⁻ (glyzFourierMarginal (𝓕 (f : WithLp 2 (H × V) → ℂ)) z) = glyzSliceSchwartz f z := by
  funext x
  have hf : Integrable (𝓕 (f : WithLp 2 (H × V) → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 f : SchwartzMap (WithLp 2 (H × V)) ℂ).integrable
  rw [fourierInv_glyzFourierMarginal hf]
  exact congrFun (f.continuous.fourierInv_fourier_eq f.integrable hf) (WithLp.toLp 2 (x, z))

end PlanarNikodym

namespace PlanarNikodym
open Filter
open scoped Topology
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem glyzSlice_fourier_support_closed (f : SchwartzMap (WithLp 2 (H × V)) ℂ)
    (z : V) {K : Set H} (hK : IsClosed K)
    (hsupp : Function.support (𝓕 (f : WithLp 2 (H × V) → ℂ)) ⊆
      {q | (WithLp.ofLp q).1 ∈ K}) :
    Function.support (𝓕 (glyzSliceSchwartz f z : H → ℂ)) ⊆ K := by
  have hf : Integrable (𝓕 (f : WithLp 2 (H × V) → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 f : SchwartzMap (WithLp 2 (H × V)) ℂ).integrable
  let M := glyzFourierMarginal (𝓕 (f : WithLp 2 (H × V) → ℂ)) z
  have hM : Integrable M := integrable_glyzFourierMarginal hf z
  have hinv : 𝓕⁻ M = (glyzSliceSchwartz f z : H → ℂ) := fourierInv_glyzFourierMarginal_fourier f z
  have hFM : Integrable (𝓕 M) := by
    have he : 𝓕 M = fun x : H => glyzSliceSchwartz f z (-x) := by
      funext x
      calc
        _ = 𝓕⁻ M (-x) := by rw [fourierInv_eq_fourier_neg, neg_neg]
        _ = _ := congrFun hinv (-x)
    rw [he]
    exact ((glyzSliceSchwartz f z).compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv).integrable
  have hzero (u : H) (hu : u ∉ K) : M u = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with η
    have hz : 𝓕 (f : WithLp 2 (H × V) → ℂ) (WithLp.toLp 2 (u, η)) = 0 := by
      by_contra hn
      have hs := hsupp hn
      exact hu hs
    simp [hz]
  intro ξ hξ
  by_contra hξK
  have heq : M =ᶠ[𝓝 ξ] fun _ => 0 := by
    filter_upwards [hK.isOpen_compl.mem_nhds hξK] with u hu
    exact hzero u hu
  have h := hM.fourier_fourierInv_eq hFM heq.continuousAt
  rw [hinv, hzero ξ hξK] at h
  exact hξ h

theorem glyzSlice_fourier_support_projection (f : SchwartzMap (WithLp 2 (H × V)) ℂ)
    (z : V) {S : Set (WithLp 2 (H × V))} (hS : IsCompact S)
    (hsupp : Function.support (𝓕 (f : WithLp 2 (H × V) → ℂ)) ⊆ S) :
    Function.support (𝓕 (glyzSliceSchwartz f z : H → ℂ)) ⊆
      (fun q : WithLp 2 (H × V) => (WithLp.ofLp q).1) '' S := by
  apply glyzSlice_fourier_support_closed f z
    (hS.image (WithLp.prodContinuousLinearEquiv 2 ℝ H V).continuous.fst).isClosed
  intro q hq
  exact ⟨q, hsupp hq, rfl⟩

end PlanarNikodym

namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def glyzSubspaceSlice (K : Submodule ℝ E) (f : SchwartzMap E ℂ) (z : Kᗮ) :
    SchwartzMap K ℂ :=
  glyzSliceSchwartz (f.compCLMOfContinuousLinearEquiv ℂ
    K.orthogonalDecomposition.symm.toContinuousLinearEquiv) z

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem glyzSubspaceSlice_apply (K : Submodule ℝ E) (f : SchwartzMap E ℂ)
    (z : Kᗮ) (x : K) : glyzSubspaceSlice K f z x = f ((x : E) + z) := by
  simp [glyzSubspaceSlice, Submodule.orthogonalDecomposition_symm_apply]

theorem glyzSubspaceSlice_fourier_support (K : Submodule ℝ E) (f : SchwartzMap E ℂ)
    (z : Kᗮ) {S : Set E} (hS : IsCompact S)
    (hsupp : Function.support (𝓕 (f : E → ℂ)) ⊆ S) :
    Function.support (𝓕 (glyzSubspaceSlice K f z : K → ℂ)) ⊆
      K.orthogonalProjectionOnto '' S := by
  let A := K.orthogonalDecomposition
  let g := f.compCLMOfContinuousLinearEquiv ℂ A.symm.toContinuousLinearEquiv
  have hg : Function.support (𝓕 (g : WithLp 2 (K × Kᗮ) → ℂ)) ⊆ A '' S := by
    intro q hq
    have hq' : 𝓕 (f : E → ℂ) (A.symm q) ≠ 0 := by
      change 𝓕 ((f : E → ℂ) ∘ A.symm) q ≠ 0 at hq
      rwa [fourier_comp_linearIsometry] at hq
    exact ⟨A.symm q, hsupp hq', A.apply_symm_apply q⟩
  have hs := glyzSlice_fourier_support_projection g z (hS.image A.continuous) hg
  intro ξ hξ
  obtain ⟨q, ⟨η, hη, rfl⟩, he⟩ := hs hξ
  refine ⟨η, hη, ?_⟩
  simpa only [A, Submodule.orthogonalDecomposition_apply, WithLp.ofLp_toLp] using he

end PlanarNikodym

namespace PlanarNikodym
open Metric

theorem isCompact_glyzFrequencyBox {m : ℕ} (L : GlyzSpace m ≃L[ℝ] GlyzSpace m)
    (a : GlyzSpace m) (R : ℝ) : IsCompact (glyzFrequencyBox L a R) := by
  rw [glyzFrequencyBox_eq_image]
  exact (isCompact_closedBall (0 : Base m) R).image
    (continuous_const.add (L.continuous.comp (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous))

theorem glyzMoment_subspace_slice_support (m : ℕ) (c δ : ℝ) (hδ : 0 < δ)
    (K : Submodule ℝ (GlyzSpace m)) (f : SchwartzMap (GlyzSpace m) ℂ) (z : Kᗮ)
    (hsupp : Function.support (𝓕 (f : GlyzSpace m → ℂ)) ⊆ glyzMomentFrequencyBox m c δ hδ) :
    Function.support (𝓕 (glyzSubspaceSlice K f z : K → ℂ)) ⊆
      K.orthogonalProjectionOnto '' glyzMomentFrequencyBox m c δ hδ := by
  exact glyzSubspaceSlice_fourier_support K f z (isCompact_glyzFrequencyBox _ _ _) hsupp

end PlanarNikodym
