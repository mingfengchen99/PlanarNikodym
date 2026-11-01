import PlanarNikodym.Geometry.PolynomialThomRootCodes
import PlanarNikodym.Geometry.ContinuousPolynomialJets
import PlanarNikodym.Geometry.CompactFiberNeighborhood

/-! Canonical roots selected by their actual Thom code are continuous on
the exact parameter locus where that code occurs. Repeated roots are included;
the proof uses the proved weak-code singleton and a uniform Cauchy bound. -/
noncomputable section
open Set Filter Polynomial Metric
open scoped Topology
namespace PlanarNikodym

variable {E : Type*}

def polynomialThomRootDomain {m : ℕ} (a : E → Fin m → ℝ)
    (s : Fin (m + 1) → Fin 3) : Set E :=
  {x | ∃ t, (weierstrassPolynomial (a x)).eval t = 0 ∧
    polynomialThomCode (weierstrassPolynomial (a x)) m t = s}

def polynomialThomRoot {m : ℕ} (a : E → Fin m → ℝ)
    (s : Fin (m + 1) → Fin 3) (x : E) : ℝ := by
  classical
  exact if hx : x ∈ polynomialThomRootDomain a s then Classical.choose hx else 0

theorem polynomialThomRoot_spec {m : ℕ} (a : E → Fin m → ℝ)
    (s : Fin (m + 1) → Fin 3) {x : E} (hx : x ∈ polynomialThomRootDomain a s) :
    (weierstrassPolynomial (a x)).eval (polynomialThomRoot a s x) = 0 ∧
      polynomialThomCode (weierstrassPolynomial (a x)) m (polynomialThomRoot a s x) = s := by
  classical
  simp only [polynomialThomRoot, dif_pos hx]
  exact Classical.choose_spec hx

theorem polynomialThomRoot_graph_iff {m : ℕ} (a : E → Fin m → ℝ)
    (s : Fin (m + 1) → Fin 3) {x : E} (hx : x ∈ polynomialThomRootDomain a s) (t : ℝ) :
    ((weierstrassPolynomial (a x)).eval t = 0 ∧
      polynomialThomCode (weierstrassPolynomial (a x)) m t = s) ↔
        t = polynomialThomRoot a s x := by
  constructor
  · rintro ⟨ht, hc⟩
    exact polynomialThomCode_injective_on_roots _ m (weierstrassPolynomial_monic _).ne_zero
      (by rw [weierstrassPolynomial_natDegree]) ht (polynomialThomRoot_spec a s hx).1
      (hc.trans (polynomialThomRoot_spec a s hx).2.symm)
  · rintro rfl
    exact polynomialThomRoot_spec a s hx

variable [TopologicalSpace E]

/-- The analytic and simple-root hypotheses are unnecessary for continuity:
continuous coefficients and a fixed actual full Thom code suffice. -/
theorem continuousWithinAt_of_weierstrass_root_thom_code
    {m : ℕ} (a : E → Fin m → ℝ) (D : Set E) (r : E → ℝ)
    (s : Fin (m + 1) → Fin 3) (x₀ : E) (ha : ContinuousAt a x₀)
    (hx₀ : x₀ ∈ D)
    (hr : ∀ x ∈ D, (weierstrassPolynomial (a x)).eval (r x) = 0)
    (hs : ∀ x ∈ D, polynomialThomCode (weierstrassPolynomial (a x)) m (r x) = s) :
    ContinuousWithinAt r D x₀ := by
  classical
  apply Metric.continuousWithinAt_iff'.mpr
  intro ε hε
  obtain ⟨V, R, hV, hxV, hR, hbound⟩ :=
    exists_open_nhds_uniform_weierstrass_root_bound a x₀ ha
  let K : Set ℝ := Icc (-R) R \ ball (r x₀) ε
  have hK : IsCompact K := isCompact_Icc.diff isOpen_ball
  let B : E × ℝ → Prop := fun z => ∀ k : Fin (m + 1),
    polynomialSignCondition true (s k)
      ((derivative^[k.val] (weierstrassPolynomial (a z.1))).eval z.2)
  have hsingle : polynomialThomCodeCell true (weierstrassPolynomial (a x₀)) m s = {r x₀} := by
    rw [← hs x₀ hx₀]
    exact polynomialThomCodeCell_weak_root_singleton _ m
      (weierstrassPolynomial_monic _).ne_zero (by rw [weierstrassPolynomial_natDegree])
      (r x₀) (hr x₀ hx₀)
  have hlocal (t : ℝ) (ht : t ∈ K) : ∀ᶠ z in 𝓝 (x₀, t), ¬ B z := by
    have hn : ¬ B (x₀, t) := by
      intro hb
      have he : t = r x₀ := Set.mem_singleton_iff.mp (hsingle ▸ hb)
      exact ht.2 (he ▸ mem_ball_self hε)
    obtain ⟨k, hk⟩ := not_forall.mp hn
    have hc := continuousAt_joint_weierstrassPolynomial_iterate_derivative_eval a x₀ t ha k.val
    have hev : ∀ᶠ z : E × ℝ in 𝓝 (x₀, t),
        ¬ polynomialSignCondition true (s k)
          ((derivative^[k.val] (weierstrassPolynomial (a z.1))).eval z.2) :=
      hc.preimage_mem_nhds ((isClosed_polynomialWeakSignCondition (s k)).isOpen_compl.mem_nhds hk)
    filter_upwards [hev] with z hz
    exact fun hb => hz (hb k)
  obtain ⟨U, hU, hxU, hexclude⟩ :=
    exists_open_nhds_compact_fiber_property (fun z => ¬ B z) x₀ K hK hlocal
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV),
    mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU), self_mem_nhdsWithin] with x hxV hxU hxD
  have hball : r x ∈ ball (r x₀) ε := by
    by_contra hn
    have hRroot := abs_lt.mp (hbound x hxV (r x) (hr x hxD))
    have hmem : r x ∈ K := ⟨⟨hRroot.1.le, hRroot.2.le⟩, hn⟩
    apply hexclude x hxU (r x) hmem
    intro k
    apply polynomialSignCondition_weaken
    exact congrFun (hs x hxD) k
  exact mem_ball.mp hball

/-- The root and its occurrence locus are constructed from the original
polynomial coefficients. Continuity includes all repeated-root parameters
where the selected actual Thom code remains present. -/
theorem continuousOn_polynomialThomRoot {m : ℕ} (a : E → Fin m → ℝ)
    (U : Set E) (hU : IsOpen U) (ha : ContinuousOn a U)
    (s : Fin (m + 1) → Fin 3) :
    ContinuousOn (polynomialThomRoot a s) (U ∩ polynomialThomRootDomain a s) := by
  intro x hx
  apply continuousWithinAt_of_weierstrass_root_thom_code a
    (U ∩ polynomialThomRootDomain a s) (polynomialThomRoot a s) s x
    ((ha x hx.1).continuousAt (hU.mem_nhds hx.1)) hx
  · intro y hy
    exact (polynomialThomRoot_spec a s hy.2).1
  · intro y hy
    exact (polynomialThomRoot_spec a s hy.2).2

end PlanarNikodym
