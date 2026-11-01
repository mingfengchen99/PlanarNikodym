import PlanarNikodym.Geometry.CommonAnalyticPolynomialFamilyRootTests
import PlanarNikodym.Geometry.ContinuousRootOwnership
import PlanarNikodym.Geometry.AnalyticCylindricalPartition

/-! The all-parameter polynomial lifting step: finitely many common-domain
analytic tests suffice for a connected, disjoint, sign-invariant graph/band
partition over every connected sign-invariant base subset. Repeated roots,
shared roots, zero discriminants and degree-zero members are included. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology BigOperators
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual common-domain finite tests whose connected sign-invariant base
subsets admit the complete simultaneous graph/band partition below. -/
def HasAnalyticPolynomialCylindricalTests
    {J : Type} [Fintype J] (m : J → ℕ) (a : (j : J) → E → Fin (m j) → ℝ)
    (U : Set E) (R : ℝ) : Prop :=
    ∃ (κ : Type) (_ : Fintype κ) (g : κ → E → ℝ),
      (∀ k, AnalyticOnNhd ℝ (g k) U) ∧
      ∀ C : Set E, C ⊆ U → IsConnected C →
        (∀ k x, x ∈ C → ∀ y, y ∈ C → oneDimensionalSign (g k x) = oneDimensionalSign (g k y)) →
        ∃ (n : ℕ) (ρ : Fin n → E → ℝ),
          n ≤ ∑ j, m j ∧ (∀ i, AnalyticOnNhd ℝ (ρ i) C) ∧
          (∀ x ∈ C, StrictMono (fun i => ρ i x)) ∧
          (∀ x ∈ C, ∀ i, ρ i x ∈ Ioo (-R) R) ∧
          (∀ x ∈ C, ∀ t : ℝ, (∃ j, (weierstrassPolynomial (a j x)).eval t = 0) ↔ ∃ i, t = ρ i x) ∧
          (⋃ i, analyticCylindricalCell C (analyticRootCuts (-R) R ρ) i) = C ×ˢ Ioo (-R) R ∧
          Pairwise (fun i j => Disjoint
            (analyticCylindricalCell C (analyticRootCuts (-R) R ρ) i)
            (analyticCylindricalCell C (analyticRootCuts (-R) R ρ) j)) ∧
          (∀ i, IsConnected (analyticCylindricalCell C (analyticRootCuts (-R) R ρ) i)) ∧
          ∀ i j,
            (∀ z ∈ analyticCylindricalCell C (analyticRootCuts (-R) R ρ) i,
              (weierstrassPolynomial (a j z.1)).eval z.2 < 0) ∨
            (∀ z ∈ analyticCylindricalCell C (analyticRootCuts (-R) R ρ) i,
              (weierstrassPolynomial (a j z.1)).eval z.2 = 0) ∨
            (∀ z ∈ analyticCylindricalCell C (analyticRootCuts (-R) R ρ) i,
              0 < (weierstrassPolynomial (a j z.1)).eval z.2)

theorem exists_common_analytic_polynomial_cylindrical_tests
    {J : Type} [Fintype J] (m : J → ℕ) (a : (j : J) → E → Fin (m j) → ℝ)
    (U : Set E) (hU : IsOpen U) (ha : ∀ j, AnalyticOnNhd ℝ (a j) U)
    (R : ℝ) (hR : 0 < R)
    (hbound : ∀ x ∈ U, ∀ t : ℝ,
      (weierstrassPolynomial (weierstrassFamilyProductCoefficients m (fun y j => a j y) x)).eval t = 0 → |t| < R) :
    HasAnalyticPolynomialCylindricalTests m a U R := by
  classical
  let A := weierstrassFamilyProductCoefficients m (fun y j => a j y)
  let M : Unit ⊕ J → ℕ := Sum.elim (fun _ => ∑ j, m j) m
  let b : (j : Unit ⊕ J) → E → Fin (M j) → ℝ := fun j =>
    match j with
    | Sum.inl _ => A
    | Sum.inr j => a j
  have hb : ∀ j, AnalyticOnNhd ℝ (b j) U := by
    intro j
    rcases j with u | j
    · exact fun x hx => analyticAt_weierstrassFamilyProductCoefficients m _ x (fun j => ha j x hx)
    · exact ha j
  obtain ⟨κ, hκ, g, hg, hprep⟩ := exists_common_analytic_polynomial_family_root_tests M b U hU hb
  refine ⟨κ, hκ, g, hg, ?_⟩
  intro C hCU hC hs
  have hp := hprep C hCU hC hs
  obtain ⟨n, Ω, ρ, hn, _, hCΩ, _, hρΩ, hmΩ, hr⟩ := hp (Sum.inl ())
  have hρ : ∀ i, AnalyticOnNhd ℝ (ρ i) C := fun i x hx => hρΩ i x (hCΩ hx)
  have hm : ∀ x ∈ C, StrictMono (fun i => ρ i x) := fun x hx => hmΩ x (hCΩ hx)
  have hunion (x : E) (hx : x ∈ C) (t : ℝ) :
      (∃ j, (weierstrassPolynomial (a j x)).eval t = 0) ↔ ∃ i, t = ρ i x := by
    have ht := hr x hx t
    change (weierstrassPolynomial (A x)).eval t = 0 ↔ _ at ht
    rw [weierstrassPolynomial_familyProductCoefficients] at ht
    simpa only [Polynomial.eval_prod, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and] using ht
  have hρbound (x : E) (hx : x ∈ C) (i : Fin n) : ρ i x ∈ Ioo (-R) R := by
    exact abs_lt.mp (hbound x (hCU hx) (ρ i x) ((hr x hx _).mpr ⟨i, rfl⟩))
  choose k Ωj μ hkj hoj hCj hjU hμj hmj hjroots using fun j => hp (Sum.inr j)
  have hμ : ∀ j l, ContinuousOn (μ j l) C := fun j l x hx =>
    (hμj j l x (hCj j hx)).continuousAt.continuousWithinAt
  have hsub (j : J) (l : Fin (k j)) (x : E) (hx : x ∈ C) : ∃ i, μ j l x = ρ i x := by
    exact (hunion x hx _).mp ⟨j, (hjroots j x hx _).mpr ⟨l, rfl⟩⟩
  have hown (j : J) := exists_fixed_continuous_root_ownership C hC ρ (μ j)
    (fun i => (hρ i).continuousOn) (hμ j) (fun x hx => (hm x hx).injective) (hsub j)
  choose S hS using hown
  have hgraph (j : J) (x : E) (hx : x ∈ C) (i : Fin n) :
      (weierstrassPolynomial (a j x)).eval (ρ i x) = 0 ↔ i ∈ S j :=
    (hjroots j x hx (ρ i x)).trans (hS j x hx i)
  let c := analyticRootCuts (-R) R ρ
  have hc := strictMono_analyticRootCuts (-R) R ρ (by linarith) hm hρbound
  have hca := analyticOnNhd_analyticRootCuts (-R) R ρ hρ
  have hband : analyticBand C (c 0) (c (Fin.last (n + 1))) = C ×ˢ Ioo (-R) R := by
    simp only [c, analyticRootCuts_zero, analyticRootCuts_last]
    rfl
  have hsign := analyticCylindricalCell_family_sign_constant c hC hca hc
    (fun j z => (weierstrassPolynomial (a j z.1)).eval z.2)
    (fun j z hz => (analyticAt_joint_weierstrassPolynomial_eval (a j) z.1 z.2
      (ha j z.1 (hCU hz.1))).continuousAt.continuousWithinAt)
    (fun j z hz hzero => by
      obtain ⟨l, hl⟩ := (hunion z.1 hz.1 z.2).mp ⟨j, hzero⟩
      exact ⟨l, by simpa only [c, analyticRootCuts_interior] using hl⟩)
    (fun j l => by
      by_cases hl : l ∈ S j
      · left
        intro z hz
        have he : z.2 = ρ l z.1 := by simpa only [c, analyticRootCuts_interior] using hz.2
        rw [he]
        exact (hgraph j z.1 hz.1 l).mpr hl
      · right
        intro z hz hzero
        have he : z.2 = ρ l z.1 := by simpa only [c, analyticRootCuts_interior] using hz.2
        rw [he] at hzero
        exact hl ((hgraph j z.1 hz.1 l).mp hzero))
  obtain ⟨hcover, hdisjoint, hconnected⟩ :=
    analytic_ordered_root_partition (-R) R ρ (by linarith) hC hρ hm hρbound
  exact ⟨n, ρ, hn, hρ, hm, hρbound, hunion, hcover, hdisjoint, hconnected, hsign⟩

end PlanarNikodym
