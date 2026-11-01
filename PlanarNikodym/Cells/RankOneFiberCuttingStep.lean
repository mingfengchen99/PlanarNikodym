import PlanarNikodym.Geometry.StratumFiberExtremum
import PlanarNikodym.Geometry.PositiveBarrierTilt
import PlanarNikodym.Geometry.PositiveFiberMaximum
import PlanarNikodym.Rank.StratumFiberCriticalMinor

/-! The actual rank-one cutting step. A positive analytic boundary
barrier is tilted, a nontrivial ambient minor is constructed, and its
zero set retains every center fiber while strictly lowering dimension.
The subsequent finite iteration is a separate theorem. -/
noncomputable section
open Set Module
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem AnalyticStratificationChart.exists_nonzero_vertical_tangent
    {n : ℕ} (Q : AnalyticStratificationChart (Fin n → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)) (hd : 1 < Q.dim)
    {q : Fin Q.dim → ℝ} (hq : q ∈ Q.source)
    (hr : finrank ℝ (L.toLinearMap.comp (fderiv ℝ Q.map q).toLinearMap).range = 1) :
    ∃ v ∈ (fderiv ℝ Q.map q).toLinearMap.range, L v = 0 ∧ v ≠ 0 := by
  let C := L.toLinearMap.comp (fderiv ℝ Q.map q).toLinearMap
  have hker : C.ker ≠ ⊥ := by
    intro he
    have hi := LinearMap.ker_eq_bot.mp he
    have heq := LinearMap.finrank_range_of_inj hi
    rw [finrank_fin_fun] at heq
    change finrank ℝ C.range = 1 at hr
    omega
  obtain ⟨w, hw, hwn⟩ : ∃ w ∈ C.ker, w ≠ 0 := by
    by_contra! hn
    apply hker
    exact eq_bot_iff.mpr hn
  refine ⟨fderiv ℝ Q.map q w, ⟨w, rfl⟩, hw, ?_⟩
  intro he
  exact hwn ((Q.derivative_injective q hq) (by simpa only [map_zero] using he))

theorem AnalyticStratificationChart.rank_one_fiber_cutting_step
    {n : ℕ} (Q : AnalyticStratificationChart (Fin n → ℝ))
    (hQ : LocallySemianalytic Q.image) (U : Set (Fin n → ℝ))
    (hQcl : closure Q.image ⊆ U)
    (hreg : RegularStratumEquations U Q.image Q.dim)
    (L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)) (hd : 1 < Q.dim)
    (hr : ∀ q ∈ Q.source,
      finrank ℝ (L.toLinearMap.comp (fderiv ℝ Q.map q).toLinearMap).range = 1)
    (V : Set (Fin n → ℝ)) (hV : IsOpen V)
    (hS : LocallySemianalytic (Q.image ∩ V)) (hb : Bornology.IsBounded (Q.image ∩ V))
    (hcl : closure (Q.image ∩ V) ⊆ U)
    (g : (Fin n → ℝ) → ℝ) (hg : AnalyticOnNhd ℝ g U)
    (hp : ∀ x ∈ Q.image ∩ V, 0 < g x)
    (hz : ∀ x ∈ closure (Q.image ∩ V) \ (Q.image ∩ V), g x = 0) :
    ∃ Z : Set (Fin n → ℝ), Z ⊆ Q.image ∩ V ∧ LocallySemianalytic Z ∧
      Bornology.IsBounded Z ∧ dimH Z ≤ (Q.dim - 1 : ℕ) ∧
      L '' Z = L '' (Q.image ∩ V) := by
  classical
  have hQU : Q.image ⊆ U := subset_closure.trans hQcl
  let S := Q.image ∩ V
  rcases S.eq_empty_or_nonempty with he | ⟨x, hx⟩
  · refine ⟨S, Subset.rfl, hS, hb, ?_, rfl⟩
    rw [he, dimH_empty]
    exact bot_le
  · obtain ⟨v, hvT, hvL, hvn⟩ := Q.exists_nonzero_vertical_tangent L hd
      (Q.inverse_mem_source hx.1) (hr _ (Q.inverse_mem_source hx.1))
    obtain ⟨g', hg', hp', hz', hvg'⟩ := exists_positive_barrier_tilt hb
      (fun z hz => hQU hz.1) g hg hp hz hx v hvn
    obtain ⟨h, hha, hdense, hcrit⟩ := Q.exists_fiber_critical_minor U hQU hreg L 1 hr
      g' hg' hx.1 hvT hvL hvg'
    let T := {z | z ∈ Q.image ∧ h z ≠ 0}
    let Z := S \ T
    have hTsemi : LocallySemianalytic T := hQ.inter_analytic_nonzero h (hha.mono hQcl)
    have hZsemi : LocallySemianalytic Z := hS.inter hTsemi.compl
    have hZmissing : Z ⊆ closure T \ T := fun z hz => ⟨hdense hz.1.1, hz.2⟩
    have hdimT : dimH T ≤ Q.dim := by
      rw [← Q.dimH_image]
      exact dimH_mono (fun _ ht => ht.1)
    have hpred : Q.dim - 1 + 1 = Q.dim := by omega
    have hdimZ : dimH Z ≤ (Q.dim - 1 : ℕ) :=
      (dimH_mono hZmissing).trans (hTsemi.dimH_missing_boundary_le (Q.dim - 1)
        (by simpa only [hpred] using hdimT))
    refine ⟨Z, fun _ hz => hz.1, hZsemi, hb.subset (fun _ hz => hz.1), hdimZ, ?_⟩
    apply Subset.antisymm (image_mono (fun _ hz => hz.1))
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨y, hy, hLy, _, hmax⟩ := exists_positive_fiber_maximum hb L L.continuous
      g' (hg'.continuousOn.mono hcl) hp' hz' ha
    have hmy : IsMaxOn g' {z | z ∈ Q.image ∩ V ∧ L z = L y} y := by
      intro z hz
      exact hmax z (subset_closure hz.1) (hz.2.trans hLy)
    have hhy : h y = 0 := hcrit y hy.1 (fun w hwT hwL =>
      Q.rank_one_fiber_extremum L hr hQU g' hg' hV hy hmy hwT hwL)
    refine ⟨y, ⟨hy, ?_⟩, hLy⟩
    intro hyT
    exact hyT.2 hhy

end PlanarNikodym
