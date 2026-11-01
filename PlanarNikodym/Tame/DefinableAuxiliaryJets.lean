import PlanarNikodym.Cells.AuxiliarySingularJets
import PlanarNikodym.Tame.DefinableRankMinors
import PlanarNikodym.Tame.DefinableCoordinateJets

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set

namespace PlanarNikodym

theorem RanDefinableOn.parameter_directionalDerivative {d : ℕ}
    {f : Parameters 2 d → ℝ} {W : Set (Parameters 2 d)}
    (hf : RanDefinableOn (f ∘ ranParameterEquiv d) (ranParameterEquiv d ⁻¹' W))
    (hW : RanDefinable (ranParameterEquiv d ⁻¹' W))
    (ho : IsOpen W) (ha : AnalyticOnNhd ℝ f W) (v : Parameters 2 d) :
    RanDefinableOn (fun x => fderiv ℝ f (ranParameterEquiv d x) v)
      (ranParameterEquiv d ⁻¹' W) := by
  let E := ranParameterEquiv d
  have hd (x : RanParameterIndex d → ℝ) (hx : x ∈ E ⁻¹' W) :
      DifferentiableAt ℝ (f ∘ E) x :=
    (ha (E x) hx).differentiableAt.comp x E.differentiableAt
  apply (hf.directionalDerivative hW (ho.preimage E.continuous) hd (E.symm v)).congr
  intro x hx
  change fderiv ℝ (f ∘ E) x (E.symm v) = fderiv ℝ f (E x) v
  rw [fderiv_comp x (ha (E x) hx).differentiableAt E.differentiableAt,
    E.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, E.apply_symm_apply]

/-- All pure auxiliary jets used by singular resolution have actual
definable graphs, even when the ambient extension is arbitrary. -/
theorem RanDefinableOn.auxiliaryJet {d : ℕ}
    {f : Parameters 2 d → ℝ} {W : Set (Parameters 2 d)}
    (hf : RanDefinableOn (f ∘ ranParameterEquiv d) (ranParameterEquiv d ⁻¹' W))
    (hW : RanDefinable (ranParameterEquiv d ⁻¹' W))
    (ho : IsOpen W) (ha : AnalyticOnNhd ℝ f W)
    (k : ℕ) (s : Fin k → Fin d) :
    RanDefinableOn (auxiliaryJet f k s ∘ ranParameterEquiv d)
      (ranParameterEquiv d ⁻¹' W) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    have hjet := ih (Fin.tail s)
    apply (hjet.parameter_directionalDerivative hW ho
      (auxiliaryJet_analytic ho ha k (Fin.tail s)) (0, Pi.single (s 0) 1)).congr
    intro x hx
    have he := auxiliaryJet_cons_of_differentiable ha (Fin.tail s) (s 0) hx
      (auxiliaryJet_analytic ho ha k (Fin.tail s) (ranParameterEquiv d x) hx).differentiableAt
    rw [Fin.cons_self_tail] at he
    exact he.symm

theorem ranDefinable_regular_auxiliaryJet_zero_locus {d k : ℕ}
    {f : Parameters 2 d → ℝ} {W : Set (Parameters 2 d)}
    (hf : RanDefinableOn (f ∘ ranParameterEquiv d) (ranParameterEquiv d ⁻¹' W))
    (hW : RanDefinable (ranParameterEquiv d ⁻¹' W))
    (ho : IsOpen W) (ha : AnalyticOnNhd ℝ f W)
    (s : Fin k → Fin d) (j : Fin d) :
    RanDefinable {x : RanParameterIndex d → ℝ |
      ranParameterEquiv d x ∈ W ∧ auxiliaryJet f k s (ranParameterEquiv d x) = 0 ∧
        fderiv ℝ (auxiliaryJet f k s) (ranParameterEquiv d x) (0, Pi.single j 1) ≠ 0} := by
  have hjet := hf.auxiliaryJet hW ho ha k s
  have hder := hjet.parameter_directionalDerivative hW ho (auxiliaryJet_analytic ho ha k s)
    (0, Pi.single j 1)
  have hz := (hjet.zeroExtension hW).setOf_eq (ranDefinableFun_const 0)
  convert hz.inter (hder.nonzero hW) using 1
  ext x
  simp only [mem_setOf_eq, mem_inter_iff, mem_preimage]
  by_cases hx : ranParameterEquiv d x ∈ W
  · simp [ranZeroExtension, hx]
  · simp [hx]

end PlanarNikodym
