import PlanarNikodym.Geometry.FiniteAnalyticGermPreparation
import PlanarNikodym.Geometry.AnalyticSignRefinementCoordinates

/-! A common prepared cylinder localized inside an arbitrary prescribed
neighborhood. Shrinking preserves the factors and their nonvanishing; no
root-confinement claim is made for the smaller vertical interval. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace PlanarNikodym

theorem exists_localized_finite_analytic_germ_preparation
    {d : ℕ} {J : Type} [Fintype J]
    (f : J → (Fin (d + 1) → ℝ) → ℝ) (x₀ : Fin (d + 1) → ℝ)
    (ha : ∀ j, AnalyticAt ℝ (f j) x₀)
    (O : Set (Fin (d + 1) → ℝ)) (hO : IsOpen O) (hxO : x₀ ∈ O) :
    ∃ (e : ((Fin d → ℝ) × ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) (ε r : ℝ),
      0 < ε ∧ 0 < r ∧
      (∀ z ∈ ball 0 ε ×ˢ Ioo (-r) r, x₀ + e z ∈ O) ∧
      (∀ j, AnalyticOnNhd ℝ (fun z => f j (x₀ + e z)) (ball 0 ε ×ˢ Ioo (-r) r)) ∧
      ∀ j, (∀ z ∈ ball 0 ε ×ˢ Ioo (-r) r, f j (x₀ + e z) = 0) ∨
        ∃ (m : ℕ) (a : (Fin d → ℝ) → Fin m → ℝ)
          (u : ((Fin d → ℝ) × ℝ) → ℝ),
          AnalyticOnNhd ℝ a (ball 0 ε) ∧
          (∀ z ∈ ball 0 ε ×ˢ Ioo (-r) r, u z ≠ 0) ∧
          ∀ z ∈ ball 0 ε ×ˢ Ioo (-r) r,
            f j (x₀ + e z) = (weierstrassPolynomial (a z.1)).eval z.2 * u z := by
  classical
  obtain ⟨e, ε, r, hε, hr, hprep⟩ := exists_finite_analytic_germ_preparation f x₀ ha
  let S : Set (Fin (d + 1) → ℝ) := O ∩ ⋂ j, {x | AnalyticAt ℝ (f j) x}
  have hS : IsOpen S := hO.inter (isOpen_iInter_of_finite (fun j => isOpen_analyticAt ℝ (f j)))
  have hxS : x₀ ∈ S := ⟨hxO, mem_iInter.mpr ha⟩
  have hT : Continuous (fun z : (Fin d → ℝ) × ℝ => x₀ + e z) :=
    continuous_const.add e.continuous
  have he0 : e (0, 0) = 0 := map_zero e
  have hN : {z : (Fin d → ℝ) × ℝ | x₀ + e z ∈ S} ∈ 𝓝 (0, 0) :=
    hT.continuousAt.preimage_mem_nhds (hS.mem_nhds (by simpa only [he0, add_zero] using hxS))
  obtain ⟨U, V, hU, h0U, hV, h0V, hUV⟩ := mem_nhds_prod_iff'.mp hN
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  obtain ⟨q, hq, hqV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
  let ε' := min ε δ
  let r' := min r q
  have hε' : 0 < ε' := lt_min hε hδ
  have hr' : 0 < r' := lt_min hr hq
  have hbase {x : Fin d → ℝ} (hx : x ∈ ball 0 ε') : x ∈ ball 0 ε ∧ x ∈ U :=
    ⟨ball_subset_ball (min_le_left ε δ) hx,
      hδU (ball_subset_ball (min_le_right ε δ) hx)⟩
  have hvert {t : ℝ} (ht : t ∈ Ioo (-r') r') : t ∈ Ioo (-r) r ∧ t ∈ V := by
    have ht' := abs_lt.mpr ht
    refine ⟨abs_lt.mp (ht'.trans_le (min_le_left r q)), hqV ?_⟩
    simpa only [mem_ball, Real.dist_eq, sub_zero] using ht'.trans_le (min_le_right r q)
  have hsub {z : (Fin d → ℝ) × ℝ} (hz : z ∈ ball 0 ε' ×ˢ Ioo (-r') r') :
      z ∈ ball 0 ε ×ˢ Ioo (-r) r := ⟨(hbase hz.1).1, (hvert hz.2).1⟩
  have hsource {z : (Fin d → ℝ) × ℝ} (hz : z ∈ ball 0 ε' ×ˢ Ioo (-r') r') :
      x₀ + e z ∈ S := hUV ⟨(hbase hz.1).2, (hvert hz.2).2⟩
  refine ⟨e, ε', r', hε', hr', (fun z hz => (hsource hz).1), ?_, ?_⟩
  · intro j z hz
    have hchart : AnalyticAt ℝ (fun w : (Fin d → ℝ) × ℝ => x₀ + e w) z :=
      analyticAt_const.add (e.analyticAt z)
    exact AnalyticAt.comp (f := fun w : (Fin d → ℝ) × ℝ => x₀ + e w)
      (g := f j) (mem_iInter.mp (hsource hz).2 j) hchart
  · intro j
    rcases hprep j with hz | ⟨m, a, u, ha', _, _, hun, hfactor, _⟩
    · exact Or.inl (fun z hz' => hz z (hsub hz'))
    · exact Or.inr ⟨m, a, u, (fun x hx => ha' x (hbase hx).1),
        (fun z hz => hun z (hsub hz)), (fun z hz => hfactor z (hsub hz))⟩

end PlanarNikodym
