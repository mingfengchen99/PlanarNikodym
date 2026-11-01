import PlanarNikodym.Analysis.Fourier.MovingCinematicBounds
import PlanarNikodym.Analysis.Fourier.RescaledTaylorAmplitude

/-! Complete mixed-jet control survives the actual joint inverse chart
and the inverse anisotropic dilation, on the expanding target domain. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace PlanarNikodym

abbrev CinematicAmplitudeVariables (d n : ℕ) :=
  (((ℝ × Aux (d + 2)) × Aux (n + 1)) × (ℝ × ℝ))

theorem norm_iteratedFDeriv_comp_contraction_equiv
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E ≃L[ℝ] E) (hL : ‖L.toContinuousLinearMap‖ ≤ 1) (f : E → F) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => f (L y)) x‖ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ := by
  have he := L.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := x) (mem_univ _) j
  simp only [preimage_univ, iteratedFDerivWithin_univ, Function.comp_def] at he
  rw [he]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ * ∏ _ : Fin j, ‖L.toContinuousLinearMap‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ * 1 := mul_le_mul_of_nonneg_left
      (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL)) (norm_nonneg _)
    _ = _ := mul_one _

def inverseCoefficientVariables (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (n : ℕ) (δ : ℝ) (hδ : δ ≠ 0) :
    ((P × Aux (n + 1)) × (ℝ × ℝ)) ≃L[ℝ] ((P × Aux (n + 1)) × (ℝ × ℝ)) :=
  ((ContinuousLinearEquiv.refl ℝ P).prodCongr (lowerDegreeDilation n δ hδ).symm).prodCongr
    (ContinuousLinearEquiv.refl ℝ (ℝ × ℝ))

theorem norm_inverseCoefficientVariables_le_one {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] (n : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ‖(inverseCoefficientVariables P n δ hδ.ne').toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  change max (max ‖x.1.1‖ ‖(lowerDegreeDilation n δ hδ.ne').symm x.1.2‖) ‖x.2‖ ≤
    max (max ‖x.1.1‖ ‖x.1.2‖) ‖x.2‖
  gcongr
  exact ((lowerDegreeDilation n δ hδ.ne').symm.toContinuousLinearMap.le_opNorm x.1.2).trans
    (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
      (norm_lowerDegreeDilation_symm_le_one n hδ hδ1) (norm_nonneg x.1.2)))

theorem exists_uniform_compact_family_jet_bound
    {E Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (H : E × Q → ℂ) {K : Set E} {S : Set Q} (hK : IsCompact K) (hS : IsCompact S)
    (hH : ∀ x ∈ K ×ˢ S, ContDiffAt ℝ ∞ H x) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ S, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (fun y => H (y, q)) x‖ ≤ C := by
  have hc : ContinuousOn (fun x : E × Q => iteratedFDeriv ℝ j (fun y => H (y, x.2)) x.1)
      (K ×ˢ S) := fun x hx => (contDiffAt_fiber_iteratedFDeriv j (hH x hx)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (hK.prod hS).exists_bound_of_continuousOn hc
  exact ⟨|C|, abs_nonneg _, fun q hq x hx => (hC (x, q) ⟨hx, hq⟩).trans (le_abs_self C)⟩

def inverseChartTaylorAmplitude {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (σ : Fin (n + 1) ↪ Fin (d + 2))
    (a : Parameters 2 d × ℝ × ℝ → ℂ) (Φ : Parameters 2 d × ℝ → ℝ)
    (q : (CinematicAmplitudeVariables d n × (ℝ × ℝ))) : ℂ :=
  rescaledTaylorAmplitude a Φ n
    (((parameterFrame d (q.1.1.1.2 + coordinateInsertion σ (e.symm q.1.1).2),
      q.1.1.1.1, q.1.2.1), q.1.2.2), q.2)

theorem contDiffAt_inverseChartTaylorAmplitude {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (σ : Fin (n + 1) ↪ Fin (d + 2))
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : Parameters 2 d × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (q : (CinematicAmplitudeVariables d n × (ℝ × ℝ)))
    (hi : AnalyticAt ℝ e.symm q.1.1) :
    ContDiffAt ℝ ∞ (inverseChartTaylorAmplitude e σ a Φ) q := by
  have hei : ContDiffAt ℝ ∞ (fun z :
      CinematicAmplitudeVariables d n × (ℝ × ℝ) => e.symm z.1.1) q :=
    hi.contDiffAt.comp q contDiffAt_fst.fst
  have hp : ContDiffAt ℝ ∞ (fun z : CinematicAmplitudeVariables d n × (ℝ × ℝ) =>
      parameterFrame d (z.1.1.1.2 + coordinateInsertion σ (e.symm z.1.1).2)) q := (parameterFrame d).contDiff.contDiffAt.comp q
    (contDiffAt_fst.fst.fst.snd.add ((coordinateInsertion σ).contDiff.contDiffAt.comp q hei.snd))
  have harg : ContDiffAt ℝ ∞ (fun z : CinematicAmplitudeVariables d n × (ℝ × ℝ) =>
      (((parameterFrame d (z.1.1.1.2 + coordinateInsertion σ (e.symm z.1.1).2),
        z.1.1.1.1, z.1.2.1), z.1.2.2), z.2)) q := ((hp.prodMk (contDiffAt_fst.fst.fst.fst.prodMk contDiffAt_fst.snd.fst)).prodMk
    contDiffAt_fst.snd.snd).prodMk contDiffAt_snd
  exact (contDiff_rescaledTaylorAmplitude ha hΦ n).contDiffAt.comp q harg

theorem exists_uniform_inverseChartTaylorAmplitude_jet_bound {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (hi : AnalyticOnNhd ℝ e.symm e.target) (σ : Fin (n + 1) ↪ Fin (d + 2))
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : Parameters 2 d × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set (CinematicAmplitudeVariables d n)}
    (hK : IsCompact K) (hKT : ∀ x ∈ K, x.1 ∈ e.target) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α ∈ Icc (0 : ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
      ∀ x : CinematicAmplitudeVariables d n, inverseCoefficientVariables (ℝ × Aux (d + 2)) n δ hδ.ne' x ∈ K →
        ‖iteratedFDeriv ℝ j (fun y => inverseChartTaylorAmplitude e σ a Φ
          (inverseCoefficientVariables (ℝ × Aux (d + 2)) n δ hδ.ne' y, α, δ)) x‖ ≤ C := by
  have hH : ∀ q ∈ K ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1),
      ContDiffAt ℝ ∞ (inverseChartTaylorAmplitude e σ a Φ) q := by
    intro q hq
    exact contDiffAt_inverseChartTaylorAmplitude e σ ha hΦ q (hi q.1.1 (hKT q.1 hq.1))
  obtain ⟨C, hC, hb⟩ := exists_uniform_compact_family_jet_bound _ hK
    (isCompact_Icc.prod isCompact_Icc) hH j
  refine ⟨C, hC, ?_⟩
  intro α hα δ hδ hδ1 x hx
  exact (norm_iteratedFDeriv_comp_contraction_equiv
    (inverseCoefficientVariables (ℝ × Aux (d + 2)) n δ hδ.ne')
    (norm_inverseCoefficientVariables_le_one (P := ℝ × Aux (d + 2)) n hδ hδ1)
    (fun y : CinematicAmplitudeVariables d n => inverseChartTaylorAmplitude e σ a Φ (y, α, δ)) j x).trans
      (hb (α, δ) ⟨hα, hδ.le, hδ1⟩ _ hx)

theorem exists_uniform_critical_inverseChartTaylorAmplitude_jet_bound {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (hi : AnalyticOnNhd ℝ e.symm e.target) (σ : Fin (n + 1) ↪ Fin (d + 2))
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : Parameters 2 d × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set (CinematicAmplitudeVariables d n)}
    (hK : IsCompact K) (hKT : ∀ x ∈ K, x.1 ∈ e.target) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, ∀ hr : 1 ≤ r,
      let δ := criticalTimeScale n r
      let hδ := criticalTimeScale_pos n (zero_lt_one.trans_le hr)
      ∀ x : CinematicAmplitudeVariables d n,
        inverseCoefficientVariables (ℝ × Aux (d + 2)) n δ hδ.ne' x ∈ K →
          ‖iteratedFDeriv ℝ j (fun y => inverseChartTaylorAmplitude e σ a Φ
            (inverseCoefficientVariables (ℝ × Aux (d + 2)) n δ hδ.ne' y,
              r * δ ^ (n + 1), δ)) x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_inverseChartTaylorAmplitude_jet_bound e hi σ ha hΦ hK hKT j
  refine ⟨C, hC, ?_⟩
  intro r hr
  dsimp only
  intro x hx
  apply hb _ ?_ _ (criticalTimeScale_pos n (zero_lt_one.trans_le hr))
    (criticalTimeScale_le_one n hr) x hx
  rw [frequency_mul_criticalTimeScale_pow n (zero_lt_one.trans_le hr)]
  exact ⟨zero_le_one, le_rfl⟩

end PlanarNikodym
