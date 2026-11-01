import PlanarNikodym.Geometry.AnalyticSimpleRootBranches
import PlanarNikodym.Geometry.AnalyticPolynomialRootBranches
import PlanarNikodym.Geometry.Cinematic

/-! A finite-multiplicity root is an analytic graph over an explicit analytic
obstruction locus in the parameter space. The obstruction locus is constructed
from actual lower vertical derivatives, and is not assumed to be regular. -/

noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual iterated derivatives in the last coordinate retain joint analyticity. -/
theorem analyticAt_vertical_iteratedDeriv
    {f : E × ℝ → ℝ} {x : E} {t : ℝ}
    (hf : AnalyticAt ℝ f (x, t)) (n : ℕ) :
    AnalyticAt ℝ (fun z : E × ℝ => iteratedDeriv n (fun s => f (z.1, s)) z.2)
      (x, t) := by
  let g : ℝ × E → ℝ := fun z => f (z.2, z.1)
  have hg : AnalyticAt ℝ g (t, x) :=
    AnalyticAt.comp (x := (t, x)) (f := fun z : ℝ × E => (z.2, z.1))
      hf (analyticAt_snd.prod analyticAt_fst)
  have hD : AnalyticAt ℝ (fun z : E × ℝ => timeDerivative g n (z.2, z.1))
      (x, t) := AnalyticAt.comp (x := (x, t)) (f := fun z : E × ℝ => (z.2, z.1))
      (timeDerivative_analyticAt hg n) (analyticAt_snd.prod analyticAt_fst)
  apply hD.congr
  filter_upwards [hf.eventually_analyticAt] with z hz
  exact timeDerivative_eq_iteratedDeriv n (z.2, z.1)
    (AnalyticAt.comp (x := (z.2, z.1)) (f := fun w : ℝ × E => (w.2, w.1))
      hz (analyticAt_snd.prod analyticAt_fst))

/-- Near a root of exact positive multiplicity `n+1`, the full multiplicity
locus is the graph of one actual analytic candidate over the common zero set
of `n` actual analytic lower-derivative obstructions. All neighborhoods are
chosen before neighboring parameters and roots. No regularity of the
obstruction zero set, or nonvanishing discriminant, is assumed. -/
theorem exists_analytic_multiplicity_root_locus
    (f : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ) (n : ℕ)
    (hf : AnalyticAt ℝ f (x₀, t₀))
    (hzero : ∀ j < n + 1, iteratedDeriv j (fun t => f (x₀, t)) t₀ = 0)
    (hn : iteratedDeriv (n + 1) (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ (U : Set E) (V : Set ℝ) (ρ : E → ℝ) (b : E → Fin n → ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧
      ρ x₀ = t₀ ∧ MapsTo ρ U V ∧ AnalyticOnNhd ℝ ρ U ∧
      AnalyticOnNhd ℝ b U ∧ b x₀ = 0 ∧
      (∀ x ∈ U, ∀ i : Fin n,
        b x i = iteratedDeriv (i : ℕ) (fun t => f (x, t)) (ρ x)) ∧
      (∀ x ∈ U, ∀ t ∈ V,
        iteratedDeriv (n + 1) (fun s => f (x, s)) t ≠ 0) ∧
      ∀ x ∈ U, ∀ t ∈ V,
        (∀ j < n + 1, iteratedDeriv j (fun s => f (x, s)) t = 0) ↔
          t = ρ x ∧ b x = 0 := by
  let D : ℕ → E × ℝ → ℝ := fun j z =>
    iteratedDeriv j (fun t => f (z.1, t)) z.2
  have hD (j : ℕ) : AnalyticAt ℝ (D j) (x₀, t₀) :=
    analyticAt_vertical_iteratedDeriv hf j
  have hDn : deriv (fun t => D n (x₀, t)) t₀ ≠ 0 := by
    simpa only [D, ← iteratedDeriv_succ] using hn
  obtain ⟨U₀, V₀, ρ, hU₀, hx₀, hV₀, ht₀, hρ₀, hρV₀, hρ, hroots⟩ :=
    exists_analytic_simple_root_branch (D n) x₀ t₀ (hD n)
      (hzero n (Nat.lt_succ_self n)) hDn
  have hnear : {z : E × ℝ | AnalyticAt ℝ f z ∧ D (n + 1) z ≠ 0}
      ∈ 𝓝 (x₀, t₀) :=
    inter_mem hf.eventually_analyticAt ((hD (n + 1)).continuousAt.eventually_ne hn)
  obtain ⟨U₁, V₁, hU₁, hx₁, hV₁, ht₁, hUV₁⟩ := mem_nhds_prod_iff'.mp hnear
  have hUmem : U₀ ∩ U₁ ∩ ρ ⁻¹' V₁ ∈ 𝓝 x₀ := by
    refine inter_mem (inter_mem (hU₀.mem_nhds hx₀) (hU₁.mem_nhds hx₁)) ?_
    apply (hρ x₀ hx₀).continuousAt.preimage_mem_nhds
    simpa only [hρ₀] using hV₁.mem_nhds ht₁
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hUmem
  let V := V₀ ∩ V₁
  let b : E → Fin n → ℝ := fun x i => D i (x, ρ x)
  have hρV : MapsTo ρ U V := fun x hx =>
    ⟨hρV₀ (hUsub hx).1.1, (hUsub hx).2⟩
  have hρU : AnalyticOnNhd ℝ ρ U := fun x hx => hρ x (hUsub hx).1.1
  have hb : AnalyticOnNhd ℝ b U := by
    intro x hx
    apply analyticAt_pi_iff.mpr
    intro i
    exact AnalyticAt.comp (x := x) (f := fun y : E => (y, ρ y))
      (analyticAt_vertical_iteratedDeriv
        (hUV₁ (show (x, ρ x) ∈ U₁ ×ˢ V₁ from
          ⟨(hUsub hx).1.2, (hρV hx).2⟩)).1 (i : ℕ))
      (analyticAt_id.prod (hρU x hx))
  refine ⟨U, V, ρ, b, hU, hxU, hV₀.inter hV₁, ⟨ht₀, ht₁⟩,
    hρ₀, hρV, hρU, hb, ?_, ?_, ?_, ?_⟩
  · funext i
    change D i (x₀, ρ x₀) = 0
    rw [hρ₀]
    exact hzero i (i.isLt.trans (Nat.lt_succ_self n))
  · intro x hx i
    rfl
  · intro x hx t ht
    exact (hUV₁ (show (x, t) ∈ U₁ ×ˢ V₁ from ⟨(hUsub hx).1.2, ht.2⟩)).2
  · intro x hx t ht
    constructor
    · intro hall
      have he : t = ρ x :=
        (hroots x (hUsub hx).1.1 t ht.1).mp (hall n (Nat.lt_succ_self n))
      refine ⟨he, ?_⟩
      funext i
      change D i (x, ρ x) = 0
      rw [← he]
      exact hall i (i.isLt.trans (Nat.lt_succ_self n))
    · rintro ⟨rfl, hb0⟩ j hj
      by_cases hjn : j < n
      · exact congrFun hb0 ⟨j, hjn⟩
      · have he : j = n := by omega
        subst j
        exact (hroots x (hUsub hx).1.1 (ρ x) (hρV hx).1).mpr rfl

/-- The explicit parameter obstruction locus projects exactly onto those
parameters admitting a nearby root with all derivatives through order `n`
zero. This is an actual elimination step, including singular parameter loci. -/
theorem exists_analytic_multiplicity_parameter_locus
    (f : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ) (n : ℕ)
    (hf : AnalyticAt ℝ f (x₀, t₀))
    (hzero : ∀ j < n + 1, iteratedDeriv j (fun t => f (x₀, t)) t₀ = 0)
    (hn : iteratedDeriv (n + 1) (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ (U : Set E) (V : Set ℝ) (b : E → Fin n → ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧
      AnalyticOnNhd ℝ b U ∧ b x₀ = 0 ∧
      ∀ x ∈ U,
        (∃ t ∈ V, ∀ j < n + 1, iteratedDeriv j (fun s => f (x, s)) t = 0) ↔
          b x = 0 := by
  obtain ⟨U, V, ρ, b, hU, hx, hV, ht, hρ₀, hρV, hρ, hb, hb₀, hbi, hn', he⟩ :=
    exists_analytic_multiplicity_root_locus f x₀ t₀ n hf hzero hn
  refine ⟨U, V, b, hU, hx, hV, ht, hb, hb₀, ?_⟩
  intro x hxU
  constructor
  · rintro ⟨t, htV, hj⟩
    exact ((he x hxU t htV).mp hj).2
  · intro hbx
    exact ⟨ρ x, hρV hxU, (he x hxU (ρ x) (hρV hxU)).mpr ⟨rfl, hbx⟩⟩

private theorem polynomial_eval_iteratedDeriv (P : ℝ[X]) (j : ℕ) :
    iteratedDeriv j (fun t => P.eval t) =
      fun t => (Polynomial.derivative^[j] P).eval t := by
  induction j generalizing P with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ', show deriv (fun t => P.eval t) =
      (fun t => P.derivative.eval t) from funext (fun t => P.deriv)]
    rw [ih, Function.iterate_succ_apply]

/-- A monic polynomial's exact finite multiplicity constructs an analytic
candidate branch and lower-derivative obstructions, also at points of the
collision determinant zero locus. Derivatives here are actual polynomial
iterates, so the statement can be used directly on algebraic multiplicity strata. -/
theorem exists_analytic_polynomial_multiplicity_root_locus
    {m : ℕ} (a : E → Fin m → ℝ) (x₀ : E) (t₀ : ℝ) (n : ℕ)
    (ha : AnalyticAt ℝ a x₀)
    (hzero : ∀ j < n + 1,
      (Polynomial.derivative^[j] (weierstrassPolynomial (a x₀))).eval t₀ = 0)
    (hn : (Polynomial.derivative^[n + 1]
      (weierstrassPolynomial (a x₀))).eval t₀ ≠ 0) :
    ∃ (U : Set E) (V : Set ℝ) (ρ : E → ℝ) (b : E → Fin n → ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧
      ρ x₀ = t₀ ∧ MapsTo ρ U V ∧ AnalyticOnNhd ℝ ρ U ∧
      AnalyticOnNhd ℝ b U ∧ b x₀ = 0 ∧
      (∀ x ∈ U, ∀ i : Fin n,
        b x i = (Polynomial.derivative^[i.val]
          (weierstrassPolynomial (a x))).eval (ρ x)) ∧
      (∀ x ∈ U, ∀ t ∈ V,
        (Polynomial.derivative^[n + 1] (weierstrassPolynomial (a x))).eval t ≠ 0) ∧
      ∀ x ∈ U, ∀ t ∈ V,
        (∀ j < n + 1,
          (Polynomial.derivative^[j] (weierstrassPolynomial (a x))).eval t = 0) ↔
          t = ρ x ∧ b x = 0 := by
  simpa only [polynomial_eval_iteratedDeriv] using
    exists_analytic_multiplicity_root_locus
      (fun z : E × ℝ => (weierstrassPolynomial (a z.1)).eval z.2) x₀ t₀ n
      (analyticAt_joint_weierstrassPolynomial_eval a x₀ t₀ ha)
      (by simpa only [polynomial_eval_iteratedDeriv] using hzero)
      (by simpa only [polynomial_eval_iteratedDeriv] using hn)

/-- For positive `n`, the constructed exact multiplicity parameter locus is
contained in the actual collision determinant zero set. This does not claim
that the determinant zero set is regular, or that its germ is nonzero. -/
theorem exists_analytic_polynomial_collision_parameter_locus
    {m : ℕ} (a : E → Fin m → ℝ) (x₀ : E) (t₀ : ℝ) (n : ℕ)
    (hnpos : 0 < n) (ha : AnalyticAt ℝ a x₀)
    (hzero : ∀ j < n + 1,
      (Polynomial.derivative^[j] (weierstrassPolynomial (a x₀))).eval t₀ = 0)
    (hn : (Polynomial.derivative^[n + 1]
      (weierstrassPolynomial (a x₀))).eval t₀ ≠ 0) :
    ∃ (U : Set E) (V : Set ℝ) (b : E → Fin n → ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧
      AnalyticOnNhd ℝ b U ∧ b x₀ = 0 ∧
      (∀ x ∈ U,
        (∃ t ∈ V, ∀ j < n + 1,
          (Polynomial.derivative^[j] (weierstrassPolynomial (a x))).eval t = 0) ↔
            b x = 0) ∧
      ∀ x ∈ U, b x = 0 → weierstrassCollisionDet (a x) = 0 := by
  obtain ⟨U, V, ρ, b, hU, hx, hV, ht, hρ₀, hρV, hρ, hb, hb₀, hbi, hn', he⟩ :=
    exists_analytic_polynomial_multiplicity_root_locus a x₀ t₀ n ha hzero hn
  have hproj (x : E) (hxU : x ∈ U) :
      (∃ t ∈ V, ∀ j < n + 1,
        (Polynomial.derivative^[j] (weierstrassPolynomial (a x))).eval t = 0) ↔
          b x = 0 := by
    constructor
    · rintro ⟨t, htV, hj⟩
      exact ((he x hxU t htV).mp hj).2
    · intro hbx
      exact ⟨ρ x, hρV hxU, (he x hxU (ρ x) (hρV hxU)).mpr ⟨rfl, hbx⟩⟩
  refine ⟨U, V, b, hU, hx, hV, ht, hb, hb₀, hproj, ?_⟩
  intro x hxU hbx
  obtain ⟨t, htV, hj⟩ := (hproj x hxU).mpr hbx
  apply weierstrassCollisionDet_eq_zero_of_multiple_root (a x) t
  · simpa only [Function.iterate_zero_apply] using hj 0 (Nat.zero_lt_succ n)
  · rw [Polynomial.deriv]
    simpa only [Function.iterate_one] using hj 1 (by omega)

end PlanarNikodym
