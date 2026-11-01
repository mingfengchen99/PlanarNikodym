import PlanarNikodym.Geometry.AnalyticFiniteLineOrders
import PlanarNikodym.Geometry.NonzeroDirectionFrame
import PlanarNikodym.Geometry.WeierstrassPreparation
import PlanarNikodym.Geometry.WeierstrassRootConfinement

/-! Common actual Weierstrass coordinates for a finite nonflat analytic germ
family. The direction, invertible frame, orders, coefficients, units and
common cylinder are constructed from the original germs. All real roots of
the prepared monic members lie in the same small vertical interval. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace PlanarNikodym

theorem exists_finite_family_weierstrass_frame
    {d : ℕ} {J : Type*} [Fintype J]
    (f : J → (Fin (d + 1) → ℝ) → ℝ) (x₀ : Fin (d + 1) → ℝ)
    (ha : ∀ j, AnalyticAt ℝ (f j) x₀)
    (hn : ∀ j, ¬ ∀ᶠ y in 𝓝 x₀, f j y = 0) :
    ∃ (e : ((Fin d → ℝ) × ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ))
      (m : J → ℕ) (a : (j : J) → (Fin d → ℝ) → Fin (m j) → ℝ)
      (u : J → ((Fin d → ℝ) × ℝ) → ℝ) (ε r : ℝ),
      0 < ε ∧ 0 < r ∧
      (∀ j, AnalyticOnNhd ℝ (a j) (ball 0 ε) ∧ a j 0 = 0) ∧
      (∀ j, AnalyticOnNhd ℝ (u j) (ball 0 ε ×ˢ Ioo (-r) r)) ∧
      (∀ j z, z ∈ ball 0 ε ×ˢ Ioo (-r) r → u j z ≠ 0) ∧
      (∀ j z, z ∈ ball 0 ε ×ˢ Ioo (-r) r →
        f j (x₀ + e z) = (weierstrassPolynomial (a j z.1)).eval z.2 * u j z) ∧
      ∀ j x, x ∈ ball 0 ε → ∀ t : ℝ,
        (weierstrassPolynomial (a j x)).eval t = 0 → |t| < r := by
  classical
  obtain ⟨v, hv, hline⟩ := exists_common_nonflat_analytic_direction f x₀ ha hn
  obtain ⟨e, he⟩ := exists_real_nonzero_direction_frame v hv
  let F (j : J) (z : (Fin d → ℝ) × ℝ) := f j (x₀ + e z)
  have hcoord : AnalyticAt ℝ (fun z : (Fin d → ℝ) × ℝ => x₀ + e z) (0, 0) :=
    analyticAt_const.add (e.analyticAt _)
  have hF (j : J) : AnalyticAt ℝ (F j) (0, 0) := by
    have h0 : e (0, 0) = 0 := map_zero e
    have ha' : AnalyticAt ℝ (f j) (x₀ + e (0, 0)) := by rw [h0, add_zero]; exact ha j
    exact AnalyticAt.comp (f := fun z : (Fin d → ℝ) × ℝ => x₀ + e z) (g := f j) ha' hcoord
  choose m hzero hm using fun j => exists_finite_analytic_line_order (hline j).1 (hline j).2
  have horders (j : J) :
      (∀ k < m j, iteratedDeriv k (fun t => F j (0, t)) 0 = 0) ∧
        iteratedDeriv (m j) (fun t => F j (0, t)) 0 ≠ 0 := by
    simpa only [F, he] using (show
      (∀ k < m j, iteratedDeriv k (fun t : ℝ => f j (x₀ + t • v)) 0 = 0) ∧
        iteratedDeriv (m j) (fun t : ℝ => f j (x₀ + t • v)) 0 ≠ 0 from ⟨hzero j, hm j⟩)
  choose U V a u hU hxU hV hxV haU ha0 hu hun hfactor using fun j =>
    exists_analytic_weierstrass_preparation_on (F j) 0 0 (m j) (hF j) (horders j).1 (horders j).2
  have hVall : {t : ℝ | ∀ j : J, t ∈ V j} ∈ 𝓝 (0 : ℝ) :=
    Filter.eventually_all.mpr (fun j => (hV j).mem_nhds (hxV j))
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hVall
  have hI (t : ℝ) (ht : t ∈ Ioo (-r) r) : ∀ j, t ∈ V j := by
    apply hrV ?_
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using ht
  choose W hW hxW hroots using fun j => exists_open_nhds_weierstrass_roots_small
    (a j) 0 ((haU j 0 (hxU j)).continuousAt) (ha0 j) r hr
  have hnear : {x : Fin d → ℝ | ∀ j : J, x ∈ U j ∩ W j} ∈ 𝓝 (0 : Fin d → ℝ) :=
    Filter.eventually_all.mpr (fun j => inter_mem ((hU j).mem_nhds (hxU j)) ((hW j).mem_nhds (hxW j)))
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hnear
  have hbase (x : Fin d → ℝ) (hx : x ∈ ball 0 ε) (j : J) : x ∈ U j ∩ W j :=
    hεU hx j
  have hprod (j : J) {z : (Fin d → ℝ) × ℝ}
      (hz : z ∈ ball 0 ε ×ˢ Ioo (-r) r) : z ∈ U j ×ˢ V j :=
    ⟨(hbase z.1 hz.1 j).1, hI z.2 hz.2 j⟩
  refine ⟨e, m, a, u, ε, r, hε, hr, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j => ⟨fun x hx => haU j x (hbase x hx j).1, ha0 j⟩
  · exact fun j z hz => hu j z (hprod j hz)
  · exact fun j z hz => hun j z (hprod j hz)
  · intro j z hz
    simpa only [sub_zero, weierstrassPolynomial_eval] using hfactor j z (hprod j hz)
  · exact fun j x hx t ht => hroots j x (hbase x hx j).2 t ht

end PlanarNikodym
