import PlanarNikodym.Geometry.AnalyticStratificationBands
import PlanarNikodym.Geometry.LocalAnalyticPolynomialCylindricalTests

/-! An actual finite analytic graph/band stratum partition over a
parametrized base stratum. Its parameters and inverses are the concrete
constructors of `AnalyticStratificationCharts` and `...Bands`. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym
namespace AnalyticStratificationChart
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cylindrical {n : ℕ} (Q : AnalyticStratificationChart E)
    (c : Fin (n + 2) → E → ℝ) (ha : ∀ i, AnalyticOnNhd ℝ (c i) Q.image)
    (hc : ∀ x ∈ Q.image, StrictMono (fun i => c i x)) :
    (Fin n ⊕ Fin (n + 1)) → AnalyticStratificationChart (E × ℝ)
  | Sum.inl i => Q.graph (c i.castSucc.succ) (ha _)
  | Sum.inr i => Q.band (c i.castSucc) (c i.succ) (ha _) (ha _)
      (fun x hx => hc x hx (by change (i : ℕ) < (i : ℕ) + 1; omega))

@[simp] theorem cylindrical_image {n : ℕ} (Q : AnalyticStratificationChart E)
    (c : Fin (n + 2) → E → ℝ) (ha : ∀ i, AnalyticOnNhd ℝ (c i) Q.image)
    (hc : ∀ x ∈ Q.image, StrictMono (fun i => c i x)) (i : Fin n ⊕ Fin (n + 1)) :
    (Q.cylindrical c ha hc i).image = analyticCylindricalCell Q.image c i := by
  cases i <;> simp only [cylindrical, graph_image, band_image, analyticCylindricalCell]

theorem cylindrical_dim_le {n : ℕ} (Q : AnalyticStratificationChart E)
    (c : Fin (n + 2) → E → ℝ) (ha : ∀ i, AnalyticOnNhd ℝ (c i) Q.image)
    (hc : ∀ x ∈ Q.image, StrictMono (fun i => c i x)) (i : Fin n ⊕ Fin (n + 1)) :
    (Q.cylindrical c ha hc i).dim ≤ Q.dim + 1 := by
  cases i <;> simp only [cylindrical, graph_dim, band_dim] <;> omega

theorem cylindrical_partition {n : ℕ} (Q : AnalyticStratificationChart E)
    (A B : ℝ) (ρ : Fin n → E → ℝ) (ha : ∀ i, AnalyticOnNhd ℝ (ρ i) Q.image)
    (hm : ∀ x ∈ Q.image, StrictMono (fun i => ρ i x))
    (hAB : A < B) (hb : ∀ x ∈ Q.image, ∀ i, ρ i x ∈ Ioo A B) :
    let c := analyticRootCuts A B ρ
    let hc := strictMono_analyticRootCuts A B ρ hAB hm hb
    let Q' := Q.cylindrical c (analyticOnNhd_analyticRootCuts A B ρ ha) hc
    (⋃ i, (Q' i).image) = Q.image ×ˢ Ioo A B ∧
      Pairwise (fun i j => Disjoint (Q' i).image (Q' j).image) := by
  dsimp only
  simp_rw [cylindrical_image]
  have h := analytic_ordered_root_partition A B ρ hAB Q.connected_image ha hm hb
  exact ⟨h.1, h.2.1⟩

end AnalyticStratificationChart

theorem HasAnalyticPolynomialCylindricalTests.exists_stratum_charts
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {J : Type} [Fintype J] {m : J → ℕ} {a : (j : J) → E → Fin (m j) → ℝ}
    {U : Set E} {R : ℝ} (hR : 0 < R)
    (H : HasAnalyticPolynomialCylindricalTests m a U R) :
    ∃ (κ : Type) (_ : Fintype κ) (g : κ → E → ℝ),
      (∀ k, AnalyticOnNhd ℝ (g k) U) ∧
      ∀ Q : AnalyticStratificationChart E, Q.image ⊆ U →
        (∀ k x, x ∈ Q.image → ∀ y, y ∈ Q.image →
          oneDimensionalSign (g k x) = oneDimensionalSign (g k y)) →
        ∃ (ι : Type) (_ : Fintype ι) (P : ι → AnalyticStratificationChart (E × ℝ)),
          (⋃ i, (P i).image) = Q.image ×ˢ Ioo (-R) R ∧
          Pairwise (fun i j => Disjoint (P i).image (P j).image) ∧
          (∀ i, (P i).dim ≤ Q.dim + 1) ∧
          ∀ i j, (∀ z ∈ (P i).image, (weierstrassPolynomial (a j z.1)).eval z.2 < 0) ∨
            (∀ z ∈ (P i).image, (weierstrassPolynomial (a j z.1)).eval z.2 = 0) ∨
            (∀ z ∈ (P i).image, 0 < (weierstrassPolynomial (a j z.1)).eval z.2) := by
  classical
  obtain ⟨κ, hκ, g, hg, htest⟩ := H
  refine ⟨κ, hκ, g, hg, ?_⟩
  intro Q hQU hs
  obtain ⟨n, ρ, _, hρ, hm, hb, _, hcover, hdisjoint, _, hsign⟩ :=
    htest Q.image hQU Q.connected_image hs
  let c := analyticRootCuts (-R) R ρ
  have hc := strictMono_analyticRootCuts (-R) R ρ (by linarith) hm hb
  have hca := analyticOnNhd_analyticRootCuts (-R) R ρ hρ
  let P := Q.cylindrical c hca hc
  refine ⟨Fin n ⊕ Fin (n + 1), inferInstance, P, ?_, ?_, ?_, ?_⟩
  · simpa only [P, AnalyticStratificationChart.cylindrical_image] using hcover
  · simpa only [P, AnalyticStratificationChart.cylindrical_image] using hdisjoint
  · exact Q.cylindrical_dim_le c hca hc
  · intro i j
    simpa only [P, AnalyticStratificationChart.cylindrical_image] using hsign i j

end PlanarNikodym
