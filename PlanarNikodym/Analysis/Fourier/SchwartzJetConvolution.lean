import PlanarNikodym.Analysis.Fourier.SchwartzConvolutionSmooth

/-! Actual full jets of Schwartz kernels and scalar convolution.
The input needs only L1 integrability; every derivative falls on the kernel. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Convolution

namespace PlanarNikodym

def schwartzJet {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : ℕ) (K : SchwartzMap Plane F) : SchwartzMap Plane (Plane [×j]→L[ℝ] F) :=
  match j with
  | 0 => SchwartzMap.postcompCLM
      (continuousMultilinearCurryFin0 ℝ Plane F).symm.toContinuousLinearEquiv.toContinuousLinearMap K
  | j + 1 => SchwartzMap.postcompCLM
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Plane) F).symm.toContinuousLinearEquiv.toContinuousLinearMap
      (SchwartzMap.fderivCLM ℝ Plane _ (schwartzJet j K))

@[simp] theorem schwartzJet_apply {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : ℕ) (K : SchwartzMap Plane F) (x : Plane) :
    schwartzJet j K x = iteratedFDeriv ℝ j K x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Plane) F).symm
      (fderiv ℝ (schwartzJet j K) x) = iteratedFDeriv ℝ (j + 1) K x
    have heq : ⇑(schwartzJet j K) = iteratedFDeriv ℝ j K := funext ih
    rw [heq]
    rfl

theorem schwartzJet_coe {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : ℕ) (K : SchwartzMap Plane F) :
    ⇑(schwartzJet j K) = iteratedFDeriv ℝ j K := funext (schwartzJet_apply j K)

set_option maxHeartbeats 800000 in
/-- Full multilinear jets of actual convolution are actual convolutions
with full kernel jets, with the complex scalar acting on the output. -/
theorem iteratedFDeriv_convolution_schwartz_smul
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [SMulCommClass ℝ ℂ F] [CompleteSpace F]
    {f : Plane → ℂ} (hf : Integrable f) (K : SchwartzMap Plane F) (j : ℕ) (x : Plane) :
    iteratedFDeriv ℝ j (f ⋆[ContinuousLinearMap.lsmul ℝ ℂ] K) x =
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℂ] (schwartzJet j K)) x := by
  induction j generalizing x with
  | zero =>
    let C := (continuousMultilinearCurryFin0 ℝ Plane F).symm.toContinuousLinearEquiv
    change C (∫ y : Plane, f y • K (x - y)) =
      ∫ y : Plane, f y • schwartzJet 0 K (x - y)
    rw [← C.integral_comp_comm (fun y : Plane => f y • K (x - y))]
    apply integral_congr_ae
    exact ae_of_all _ (fun _ => by ext v; rfl)
  | succ j ih =>
    let J := schwartzJet j K
    let L : ℂ →L[ℝ] (Plane [×j]→L[ℝ] F) →L[ℝ] (Plane [×j]→L[ℝ] F) :=
      ContinuousLinearMap.lsmul ℝ ℂ
    let C := (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (j + 1) => Plane) F).symm.toContinuousLinearEquiv
    have heq : iteratedFDeriv ℝ j (f ⋆[ContinuousLinearMap.lsmul ℝ ℂ] K) = f ⋆[L] J := funext ih
    rw [iteratedFDeriv_succ_eq_comp_left, heq]
    change C (fderiv ℝ (f ⋆[L] J) x) = _
    rw [(hasFDerivAt_convolution_schwartz L hf J x).fderiv]
    change C (∫ y : Plane, (L.precompR Plane) (f y)
      (fderiv ℝ J (x - y))) = ∫ y : Plane, f y • schwartzJet (j + 1) K (x - y)
    rw [← C.integral_comp_comm (fun y : Plane =>
      (L.precompR Plane) (f y) (fderiv ℝ J (x - y)))]
    apply integral_congr_ae
    exact ae_of_all _ (fun _ => by ext v; rfl)

theorem FrequencyCutoff.iteratedFDeriv_band_eq_integral (L : FrequencyCutoff)
    {f : Plane → ℂ} (hf : Integrable f) (j k : ℕ) (x : Plane) :
    iteratedFDeriv ℝ j (L.band k f) x =
      ∫ y : Plane, f y • iteratedFDeriv ℝ j (L.bandKernel k) (x - y) := by
  let K := inverseFourierSchwartz (L.bandSymbol k)
    (L.bandSymbol_smooth k) (L.bandSymbol_compact k)
  have heq : L.band k f = f ⋆[ContinuousLinearMap.lsmul ℝ ℂ] K := by
    funext x
    unfold FrequencyCutoff.band
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
      K, inverseFourierSchwartz_apply, FrequencyCutoff.bandKernel]
    exact integral_congr_ae (ae_of_all _ (fun y => mul_comm _ _))
  rw [heq, iteratedFDeriv_convolution_schwartz_smul hf K j x]
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, schwartzJet_apply,
    K, inverseFourierSchwartz_coe, FrequencyCutoff.bandKernel]

end PlanarNikodym
