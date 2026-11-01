import PlanarNikodym.Analysis.Maximal.E2FIONormalizedAmplitude
import PlanarNikodym.Analysis.Maximal.E2FIONormalizedGradient
import PlanarNikodym.Analysis.Maximal.E2FIONonstationaryPartition

/-! Applying actual normalized Gram amplitudes and the diagonal gradient
argument to two-dimensional nonstationary phase gives uniform decay for
the original full Gram kernel on a gradient-separating phase patch. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ComplexConjugate
set_option autoImplicit false
namespace PlanarNikodym

def e2FIOPlaneDirections (j : Fin 2) : Plane := if j = 0 then (1,0) else (0,1)

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem e2_first_coordinate_eq_parameter_gradient {Φ : Plane × P → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (p : P) (q : Plane) :
    e2FIOFirstCoordinateDerivative (fun z : P × Plane => Φ (z.2,z.1)) (p,q) =
      (e2FIOParameterGradient e2FIOPlaneDirections Φ (q,p)).1 := by
  have hq : DifferentiableAt ℝ (fun r : Plane => Φ (r,p)) q :=
    ((hΦ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)).differentiableAt
  have hp : HasDerivAt (fun s : ℝ => (s,q.2)) (1,0) q.1 :=
    (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  exact (hq.hasFDerivAt.comp_hasDerivAt q.1 hp).deriv

theorem e2_second_coordinate_eq_parameter_gradient {Φ : Plane × P → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (p : P) (q : Plane) :
    e2FIOSecondCoordinateDerivative (fun z : P × Plane => Φ (z.2,z.1)) (p,q) =
      (e2FIOParameterGradient e2FIOPlaneDirections Φ (q,p)).2 := by
  have hq : DifferentiableAt ℝ (fun r : Plane => Φ (r,p)) q :=
    ((hΦ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)).differentiableAt
  have hp : HasDerivAt (fun s : ℝ => (q.1,s)) (0,1) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  exact (hq.hasFDerivAt.comp_hasDerivAt q.2 hp).deriv

def e2FIONormalizedCoordinateHomeomorph :
    (((Plane × Plane) × ℝ) × Plane) ≃ₜ (((Plane × Plane) × Plane) × ℝ) where
  toFun z := (((z.2,z.1.1.1),z.1.1.2),z.1.2)
  invFun z := (((z.1.1.2,z.1.2),z.2),z.1.1.1)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_snd.prodMk continuous_fst.fst.fst).prodMk
    continuous_fst.fst.snd).prodMk continuous_fst.snd
  continuous_invFun := ((continuous_fst.fst.snd.prodMk continuous_fst.snd).prodMk
    continuous_snd).prodMk continuous_fst.fst.fst

theorem e2_exists_local_gram_offDiagonal_decay
    {Φ : Plane × Plane → ℝ} {a : Plane × Plane → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {O : Set (Plane × Plane)} (hO : IsOpen O) {c : ℝ} (hcpos : 0 < c)
    (hs : ∀ (q : Plane) (x y : Plane), (q,x) ∈ O → (q,y) ∈ O →
      c * ‖x-y‖ ≤ ‖e2FIOParameterGradient e2FIOPlaneDirections Φ (q,x)-
        e2FIOParameterGradient e2FIOPlaneDirections Φ (q,y)‖)
    (hsa : tsupport a ⊆ O) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), r ≠ 0 → ∀ (x y : Plane), x ≠ y →
      ‖e2FIOGramKernel volume r (fun q x => Φ (q,x)) a x y‖ ≤
        C * (|r * ‖y-x‖|⁻¹)^N := by
  obtain ⟨χ, ψ, hB, hcB, hBs, heq⟩ :=
    e2_exists_exact_normalized_gram_amplitude volume hΦ ha hc
  let e := e2FIONormalizedCoordinateHomeomorph
  let Ψ : (((Plane × Plane) × ℝ) × Plane) → ℝ := fun z =>
    e2FIONormalizedDifference Φ (e z)
  let b : (((Plane × Plane) × ℝ) × Plane) → ℂ :=
    e2FIONormalizedGramAmplitude a χ ψ ∘ e
  have hmap : ContDiff ℝ ∞ e :=
    ((contDiff_snd.prodMk contDiff_fst.fst.fst).prodMk
      contDiff_fst.fst.snd).prodMk contDiff_fst.snd
  have hΨ : ContDiff ℝ ∞ Ψ := (e2FIONormalizedDifference_contDiff hΦ).comp hmap
  have hb : ContDiff ℝ ∞ b := hB.comp hmap
  have hbc : HasCompactSupport b := hcB.comp_homeomorph e
  have hne : ∀ z ∈ tsupport b, e2FIOFirstCoordinateDerivative Ψ z ≠ 0 ∨
      e2FIOSecondCoordinateDerivative Ψ z ≠ 0 := by
    intro z hz
    have hzB := tsupport_comp_subset_preimage (e2FIONormalizedGramAmplitude a χ ψ) e.continuous hz
    have hss := e2FIONormalizedGramAmplitude_tsupport_subset a χ ψ hzB
    have hn := e2_normalized_gradient_lower_bound e2FIOPlaneDirections hΦ hO c hs
      z.2 z.1.1.1 z.1.1.2 z.1.2 (hsa hss.1) (hsa hss.2.1)
    have hv : 0 < ‖z.1.1.2‖ := lt_trans (by norm_num : (0 : ℝ) < 1/2) (hBs _ hzB)
    have hnp : 0 < ‖e2FIOParameterGradient e2FIOPlaneDirections (e2FIONormalizedPhaseOnFiber Φ)
        (z.2,z.1)‖ := lt_of_lt_of_le (mul_pos hcpos hv) hn
    have h1 := e2_first_coordinate_eq_parameter_gradient (e2FIONormalizedPhaseOnFiber_contDiff hΦ) z.1 z.2
    have h2 := e2_second_coordinate_eq_parameter_gradient (e2FIONormalizedPhaseOnFiber_contDiff hΦ) z.1 z.2
    by_cases hh1 : e2FIOFirstCoordinateDerivative Ψ z ≠ 0
    · exact Or.inl hh1
    · right
      intro hh2
      have he1 : (e2FIOParameterGradient e2FIOPlaneDirections
          (e2FIONormalizedPhaseOnFiber Φ) (z.2,z.1)).1 = 0 := h1.symm.trans (not_ne_iff.mp hh1)
      have he2 : (e2FIOParameterGradient e2FIOPlaneDirections
          (e2FIONormalizedPhaseOnFiber Φ) (z.2,z.1)).2 = 0 := h2.symm.trans hh2
      have he0 : e2FIOParameterGradient e2FIOPlaneDirections
          (e2FIONormalizedPhaseOnFiber Φ) (z.2,z.1) = 0 := Prod.ext he1 he2
      rw [he0, norm_zero] at hnp
      exact (lt_irrefl 0 hnp)
  obtain ⟨C, hC, hdec⟩ := e2_exists_uniform_two_dimensional_nonstationary_decay hΨ hb hbc hne N
  refine ⟨C, hC, ?_⟩
  intro r hr x y hxy
  have hd := hdec ((x,‖y-x‖⁻¹ • (y-x)),‖y-x‖) (r*‖y-x‖)
    (mul_ne_zero hr (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))))
  rw [heq r x y hxy]
  exact hd

end PlanarNikodym
