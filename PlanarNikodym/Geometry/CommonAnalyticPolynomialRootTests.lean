import PlanarNikodym.Geometry.CommonAnalyticSimpleSquarefreeStrata
import PlanarNikodym.Geometry.ConnectedSimplePolynomialRoots
import PlanarNikodym.Geometry.PolynomialThomSigns

/-! Finite common-domain analytic tests sufficient to prepare every real root
of an arbitrary monic analytic polynomial on each connected sign-invariant
base subset. No quantifier elimination, discriminant or multiplicity input is
assumed, and the tests are analytic on the original domain. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A common finite analytic test family controls the real roots on every
connected base subset where its signs are constant. Roots may collide at any
original parameter; the construction uses actual squarefree quotients. -/
theorem exists_common_analytic_polynomial_root_tests
    {M : ℕ} (a : E → Fin M → ℝ) (U : Set E) (hU : IsOpen U)
    (ha : AnalyticOnNhd ℝ a U) :
    ∃ (κ : Type) (_ : Fintype κ) (g : κ → E → ℝ),
      (∀ k, AnalyticOnNhd ℝ (g k) U) ∧
      ∀ C : Set E, C ⊆ U → IsConnected C →
        (∀ k x, x ∈ C → ∀ y, y ∈ C → oneDimensionalSign (g k x) = oneDimensionalSign (g k y)) →
        ∃ (n : ℕ) (Ω : Set E) (ρ : Fin n → E → ℝ),
          n ≤ M ∧ IsOpen Ω ∧ C ⊆ Ω ∧ Ω ⊆ U ∧
          (∀ i, AnalyticOnNhd ℝ (ρ i) Ω) ∧
          (∀ x ∈ Ω, StrictMono (fun i => ρ i x)) ∧
          ∀ x ∈ C, ∀ t : ℝ, (weierstrassPolynomial (a x)).eval t = 0 ↔ ∃ i, t = ρ i x := by
  classical
  obtain ⟨T⟩ := exists_common_analytic_simple_squarefree_stratification a U U hU
    (CommonAnalyticOpen.self U)
    (fun i => AnalyticFractionOn.of_analytic (fun x hx => analyticAt_pi_iff.mp (ha x hx) i))
  letI : Fintype T.Index := T.indexFintype
  choose n f g hf hg he using T.exists_common_analytic_tests
  let κ := Σ i : T.Index, Fin (n i + (T.stratum i).testCount)
  let h : κ → E → ℝ := fun k x => Fin.addCases (f k.1 x) (g k.1 x) k.2
  refine ⟨κ, inferInstance, h, ?_, ?_⟩
  · intro k x hx
    rcases k with ⟨i, k⟩
    induction k using Fin.addCases with
    | left k => simpa only [h, Fin.addCases_left] using analyticAt_pi_iff.mp (hf i x hx) k
    | right k => simpa only [h, Fin.addCases_right] using analyticAt_pi_iff.mp (hg i x hx) k
  · intro C hCU hC hs
    obtain ⟨x₀, hx₀⟩ := hC.nonempty
    obtain ⟨i, hi⟩ := (T.cover x₀).mp (hCU hx₀)
    obtain ⟨_, hn₀, hz₀⟩ := (he i x₀).mp hi
    have hCi : C ⊆ (T.stratum i).carrier := by
      intro x hx
      apply (he i x).mpr
      refine ⟨hCU hx, ?_, ?_⟩
      · intro j hz
        have hs' := hs ⟨i, Fin.castAdd (T.stratum i).testCount j⟩ x hx x₀ hx₀
        simp only [h, Fin.addCases_left] at hs'
        exact hn₀ j (oneDimensionalSign_eq_one.mp (hs'.symm.trans (oneDimensionalSign_eq_one.mpr hz)))
      · intro j
        have hs' := hs ⟨i, Fin.natAdd (n i) j⟩ x hx x₀ hx₀
        simp only [h, Fin.addCases_right] at hs'
        exact oneDimensionalSign_eq_one.mp (hs'.trans (oneDimensionalSign_eq_one.mpr (hz₀ j)))
    have hCa : C ⊆ (T.stratum i).ambient := fun x hx => T.carrier_subset_ambient i (hCi hx)
    obtain ⟨n, Ω, ρ, hnd, ho, hCΩ, hΩ, hρ, hm, hr⟩ :=
      exists_ordered_analytic_polynomial_roots_on_connected_subset
        (T.stratum i).coefficients (T.stratum i).ambient C
        (T.ambient_open i) (T.coefficients_analytic i) hCa hC
        (fun x hx => T.ambient_collision_ne_zero i x (hCa hx))
    refine ⟨n, Ω, ρ, hnd.trans (T.degree_le i), ho, hCΩ,
      fun x hx => T.ambient_subset_domain i (hΩ hx), hρ, hm, ?_⟩
    intro x hx t
    exact (T.roots_iff i x (hCi hx) t).symm.trans (hr x (hCΩ hx) t)

end PlanarNikodym
