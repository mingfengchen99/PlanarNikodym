import PlanarNikodym.Analysis.Maximal.E2FIONormalizedGramKernel
import PlanarNikodym.Analysis.Maximal.E2FIOGramDecay

/-! Uniform full Gram decay with compactly supported retained parameters.
The two-dimensional oscillatory estimate is uniform before integrating
the retained parameters. All kernels are the actual full FIO kernels. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ComplexConjugate
namespace PlanarNikodym
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [SFinite (volume : Measure V)] [IsFiniteMeasureOnCompacts (volume : Measure V)]

def retainedFIOCoordinateEquiv :
    ((V × ((Plane × Plane) × ℝ)) × Plane) ≃ₜ
      ((((V × Plane) × Plane) × Plane) × ℝ) where
  toFun z := ((((z.1.1,z.2),z.1.2.1.1),z.1.2.1.2),z.1.2.2)
  invFun z := ((z.1.1.1.1,((z.1.1.2,z.1.2),z.2)),z.1.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (((continuous_fst.fst.prodMk continuous_snd).prodMk
    continuous_fst.snd.fst.fst).prodMk continuous_fst.snd.fst.snd).prodMk
      continuous_fst.snd.snd
  continuous_invFun := (continuous_fst.fst.fst.fst.prodMk
    ((continuous_fst.fst.snd.prodMk continuous_fst.snd).prodMk continuous_snd)).prodMk
      continuous_fst.fst.fst.snd

theorem exists_retained_full_gram_offDiagonal_decay
    {Φ : (V × Plane) × Plane → ℝ} {a : (V × Plane) × Plane → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {O : Set ((V × Plane) × Plane)} (hO : IsOpen O) {c : ℝ} (hcpos : 0 < c)
    (hs : ∀ (v : V) (q x y : Plane), ((v,q),x) ∈ O → ((v,q),y) ∈ O →
      c * ‖x-y‖ ≤ ‖e2FIOParameterGradient e2FIOPlaneDirections
        (fun z : Plane × Plane => Φ ((v,z.1),z.2)) (q,x) -
        e2FIOParameterGradient e2FIOPlaneDirections
        (fun z : Plane × Plane => Φ ((v,z.1),z.2)) (q,y)‖)
    (hsa : tsupport a ⊆ O) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), r ≠ 0 → ∀ x y : Plane, x ≠ y →
      ‖e2FIOGramKernel volume r (fun q x => Φ (q,x)) a x y‖ ≤
        C * (|r * ‖y-x‖|⁻¹)^N := by
  obtain ⟨χ,ψ,hB,hcB,hBs,heq⟩ :=
    e2_exists_exact_normalized_gram_amplitude volume hΦ ha hc
  let e := retainedFIOCoordinateEquiv (V := V)
  let Ψ : ((V × ((Plane × Plane) × ℝ)) × Plane) → ℝ :=
    fun z => e2FIONormalizedDifference Φ (e z)
  let b : ((V × ((Plane × Plane) × ℝ)) × Plane) → ℂ :=
    e2FIONormalizedGramAmplitude a χ ψ ∘ e
  have hmap : ContDiff ℝ ∞ e :=
    (((contDiff_fst.fst.prodMk contDiff_snd).prodMk
      contDiff_fst.snd.fst.fst).prodMk contDiff_fst.snd.fst.snd).prodMk
        contDiff_fst.snd.snd
  have hΨ : ContDiff ℝ ∞ Ψ := (e2FIONormalizedDifference_contDiff hΦ).comp hmap
  have hb : ContDiff ℝ ∞ b := hB.comp hmap
  have hbc : HasCompactSupport b := hcB.comp_homeomorph e
  have hne : ∀ z ∈ tsupport b, e2FIOFirstCoordinateDerivative Ψ z ≠ 0 ∨
      e2FIOSecondCoordinateDerivative Ψ z ≠ 0 := by
    intro z hz
    have hzB := tsupport_comp_subset_preimage (e2FIONormalizedGramAmplitude a χ ψ) e.continuous hz
    have hss := e2FIONormalizedGramAmplitude_tsupport_subset a χ ψ hzB
    let Φv : Plane × Plane → ℝ := fun w => Φ ((z.1.1,w.1),w.2)
    have hΦv : ContDiff ℝ ∞ Φv := hΦ.comp
      ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
    let Ov : Set (Plane × Plane) := (fun w : Plane × Plane => ((z.1.1,w.1),w.2)) ⁻¹' O
    have hOv : IsOpen Ov := hO.preimage
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
    have hsv : ∀ (q x y : Plane), (q,x) ∈ Ov → (q,y) ∈ Ov →
        c * ‖x-y‖ ≤ ‖e2FIOParameterGradient e2FIOPlaneDirections Φv (q,x) -
          e2FIOParameterGradient e2FIOPlaneDirections Φv (q,y)‖ := hs z.1.1
    have hn := e2_normalized_gradient_lower_bound e2FIOPlaneDirections hΦv hOv c hsv
      z.2 z.1.2.1.1 z.1.2.1.2 z.1.2.2 (hsa hss.1) (hsa hss.2.1)
    have hv : 0 < ‖z.1.2.1.2‖ := lt_trans (by norm_num : (0 : ℝ) < 1/2) (hBs _ hzB)
    have hnp : 0 < ‖e2FIOParameterGradient e2FIOPlaneDirections
        (e2FIONormalizedPhaseOnFiber Φv) (z.2,z.1.2)‖ :=
      lt_of_lt_of_le (mul_pos hcpos hv) hn
    have h1 := e2_first_coordinate_eq_parameter_gradient
      (e2FIONormalizedPhaseOnFiber_contDiff hΦv) z.1.2 z.2
    have h2 := e2_second_coordinate_eq_parameter_gradient
      (e2FIONormalizedPhaseOnFiber_contDiff hΦv) z.1.2 z.2
    have he1 : e2FIOFirstCoordinateDerivative Ψ z =
        (e2FIOParameterGradient e2FIOPlaneDirections (e2FIONormalizedPhaseOnFiber Φv)
          (z.2,z.1.2)).1 := h1
    have he2 : e2FIOSecondCoordinateDerivative Ψ z =
        (e2FIOParameterGradient e2FIOPlaneDirections (e2FIONormalizedPhaseOnFiber Φv)
          (z.2,z.1.2)).2 := h2
    by_cases hh1 : e2FIOFirstCoordinateDerivative Ψ z ≠ 0
    · exact Or.inl hh1
    · right
      intro hh2
      have hz1 := he1.symm.trans (not_ne_iff.mp hh1)
      have hz2 := he2.symm.trans hh2
      have he0 : e2FIOParameterGradient e2FIOPlaneDirections
          (e2FIONormalizedPhaseOnFiber Φv) (z.2,z.1.2) = 0 := Prod.ext hz1 hz2
      rw [he0,norm_zero] at hnp
      exact lt_irrefl 0 hnp
  obtain ⟨C,hC,hdec⟩ := e2_exists_uniform_two_dimensional_nonstationary_decay hΨ hb hbc hne N
  let K : Set (V) := (fun z : (V × Plane) × Plane => z.1.1) '' tsupport a
  have hK : IsCompact K := hc.isCompact.image continuous_fst.fst
  let D : V → ℝ := K.indicator (fun _ => C)
  have hD : Integrable D := (integrable_indicator_iff hK.measurableSet).mpr
    (integrableOn_const hK.measure_ne_top)
  refine ⟨∫ v, D v, integral_nonneg (fun v => indicator_nonneg (fun _ _ => hC) v),?_⟩
  intro r hr x y hxy
  let θ : Plane := ‖y-x‖⁻¹ • (y-x)
  let h : ℝ := ‖y-x‖
  have hh : h ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  let F : (V × Plane) → ℂ := fun q =>
    Complex.exp (((r*h*e2FIONormalizedDifference Φ (((q,x),θ),h) : ℝ) : ℂ)*Complex.I) *
      e2FIONormalizedGramAmplitude a χ ψ (((q,x),θ),h)
  have harg : Continuous (fun q : V × Plane => (((q,x),θ),h)) :=
    ((continuous_id.prodMk continuous_const).prodMk continuous_const).prodMk continuous_const
  have hF : Continuous F :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul ((e2FIONormalizedDifference_contDiff hΦ).continuous.comp harg))).mul
        continuous_const)).mul (hB.continuous.comp harg)
  let KQ : Set (V × Plane) := Prod.fst '' tsupport a
  have hKQ : IsCompact KQ := hc.isCompact.image continuous_fst
  have hFc : HasCompactSupport F := by
    apply HasCompactSupport.intro hKQ
    intro q hq
    have haz : a (q,x) = 0 := by
      by_contra hax
      exact hq ⟨(q,x),subset_tsupport a hax,rfl⟩
    simp [F,e2FIONormalizedGramAmplitude,haz]
  have hFi : Integrable F (volume : Measure (V × Plane)) :=
    hF.integrable_of_hasCompactSupport hFc
  rw [heq r x y hxy]
  change ‖∫ q, F q‖ ≤ _
  have hFiprod : Integrable F ((volume : Measure (V)).prod (volume : Measure Plane)) := by
    rwa [← Measure.volume_eq_prod]
  rw [Measure.volume_eq_prod, integral_prod F hFiprod]
  have hbound : ∀ v : V, ‖∫ q : Plane, F (v,q)‖ ≤ D v * (|r*h|⁻¹)^N := by
    intro v
    by_cases hv : v ∈ K
    · simp only [D,indicator_of_mem hv]
      exact hdec (v,((x,θ),h)) (r*h) (mul_ne_zero hr hh)
    · have haz (q : Plane) : a ((v,q),x) = 0 := by
        by_contra hax
        exact hv ⟨((v,q),x),subset_tsupport a hax,rfl⟩
      simp [F,e2FIONormalizedGramAmplitude,haz,D,hv]
  have hnorm := norm_integral_le_of_norm_le (hD.mul_const ((|r*h|⁻¹)^N))
    (Eventually.of_forall hbound)
  simpa only [integral_mul_const] using hnorm

end PlanarNikodym
