import PlanarNikodym.Geometry.AnalyticPolynomialDivision

/-! Analytic fractions with numerators and denominators on one common
original domain. Poles are excluded only on the specified ambient subset.
Clearing these denominators produces genuine common-domain analytic tests. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def AnalyticFractionOn (U V : Set E) (f : E → ℝ) : Prop :=
  ∃ g h : E → ℝ, AnalyticOnNhd ℝ g U ∧ AnalyticOnNhd ℝ h U ∧
    (∀ x ∈ V, h x ≠ 0) ∧ ∀ x ∈ V, f x = g x / h x

namespace AnalyticFractionOn

theorem of_analytic {U V : Set E} {f : E → ℝ} (hf : AnalyticOnNhd ℝ f U) :
    AnalyticFractionOn U V f :=
  ⟨f, fun _ => 1, hf, fun _ _ => analyticAt_const, by simp, by simp⟩

theorem const (U V : Set E) (c : ℝ) : AnalyticFractionOn U V (fun _ => c) :=
  of_analytic (fun _ _ => analyticAt_const)

theorem mono {U V W : Set E} {f : E → ℝ}
    (hf : AnalyticFractionOn U V f) (hWV : W ⊆ V) : AnalyticFractionOn U W f := by
  obtain ⟨g, h, hg, hh, hn, he⟩ := hf
  exact ⟨g, h, hg, hh, fun x hx => hn x (hWV hx), fun x hx => he x (hWV hx)⟩

theorem congr {U V : Set E} {f g : E → ℝ}
    (hf : AnalyticFractionOn U V f) (hfg : EqOn f g V) : AnalyticFractionOn U V g := by
  obtain ⟨p, q, hp, hq, hn, he⟩ := hf
  exact ⟨p, q, hp, hq, hn, fun x hx => (hfg hx).symm.trans (he x hx)⟩

theorem add {U V : Set E} {f g : E → ℝ}
    (hf : AnalyticFractionOn U V f) (hg : AnalyticFractionOn U V g) :
    AnalyticFractionOn U V (fun x => f x + g x) := by
  obtain ⟨p, q, hp, hq, hqn, he⟩ := hf
  obtain ⟨r, s, hr, hs, hsn, hf⟩ := hg
  refine ⟨fun x => p x * s x + r x * q x, fun x => q x * s x,
    fun x hx => ((hp x hx).mul (hs x hx)).add ((hr x hx).mul (hq x hx)),
    fun x hx => (hq x hx).mul (hs x hx),
    fun x hx => mul_ne_zero (hqn x hx) (hsn x hx), ?_⟩
  intro x hx
  dsimp only
  rw [he x hx, hf x hx]
  field_simp [hqn x hx, hsn x hx]

theorem mul {U V : Set E} {f g : E → ℝ}
    (hf : AnalyticFractionOn U V f) (hg : AnalyticFractionOn U V g) :
    AnalyticFractionOn U V (fun x => f x * g x) := by
  obtain ⟨p, q, hp, hq, hqn, he⟩ := hf
  obtain ⟨r, s, hr, hs, hsn, hf⟩ := hg
  refine ⟨fun x => p x * r x, fun x => q x * s x,
    fun x hx => (hp x hx).mul (hr x hx), fun x hx => (hq x hx).mul (hs x hx),
    fun x hx => mul_ne_zero (hqn x hx) (hsn x hx), ?_⟩
  intro x hx
  dsimp only
  rw [he x hx, hf x hx, div_mul_div_comm]

theorem neg {U V : Set E} {f : E → ℝ} (hf : AnalyticFractionOn U V f) :
    AnalyticFractionOn U V (fun x => -f x) := by
  obtain ⟨p, q, hp, hq, hn, he⟩ := hf
  exact ⟨fun x => -p x, q, fun x hx => (hp x hx).neg, hq, hn,
    fun x hx => by dsimp only; rw [he x hx, neg_div]⟩

theorem inv {U V : Set E} {f : E → ℝ} (hf : AnalyticFractionOn U V f)
    (hn : ∀ x ∈ V, f x ≠ 0) : AnalyticFractionOn U V (fun x => (f x)⁻¹) := by
  obtain ⟨p, q, hp, hq, _, he⟩ := hf
  refine ⟨q, p, hq, hp, ?_, ?_⟩
  · intro x hx hz
    exact hn x hx (by rw [he x hx, hz, zero_div])
  · intro x hx
    dsimp only
    rw [he x hx, inv_div]

theorem div {U V : Set E} {f g : E → ℝ}
    (hf : AnalyticFractionOn U V f) (hg : AnalyticFractionOn U V g)
    (hn : ∀ x ∈ V, g x ≠ 0) : AnalyticFractionOn U V (fun x => f x / g x) := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hn)

theorem finset_sum {U V : Set E} {ι : Type*} (s : Finset ι)
    (f : ι → E → ℝ) (hf : ∀ i ∈ s, AnalyticFractionOn U V (f i)) :
    AnalyticFractionOn U V (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const U V 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem analyticOnNhd {U V : Set E} {f : E → ℝ}
    (hf : AnalyticFractionOn U V f) (hV : IsOpen V) (hVU : V ⊆ U) :
    AnalyticOnNhd ℝ f V := by
  obtain ⟨p, q, hp, hq, hn, he⟩ := hf
  intro x hx
  apply ((hp x (hVU hx)).div (hq x (hVU hx)) (hn x hx)).congr
  filter_upwards [hV.mem_nhds hx] with y hy
  exact (he y hy).symm

/-- Zero and nonzero tests can be written using a numerator analytic on
the original domain, even when the denominator vanishes outside the ambient. -/
theorem exists_common_analytic_zero_test {U V : Set E} {f : E → ℝ}
    (hf : AnalyticFractionOn U V f) :
    ∃ g : E → ℝ, AnalyticOnNhd ℝ g U ∧
      ∀ x ∈ V, (f x = 0 ↔ g x = 0) ∧ (f x ≠ 0 ↔ g x ≠ 0) := by
  obtain ⟨p, q, hp, _, hn, he⟩ := hf
  refine ⟨p, hp, ?_⟩
  intro x hx
  have hz : f x = 0 ↔ p x = 0 := by rw [he x hx, div_eq_zero_iff]; simp [hn x hx]
  exact ⟨hz, not_congr hz⟩

end AnalyticFractionOn

def analyticFractionFunctionSubring (U V : Set E) : Subring (E → ℝ) where
  carrier := {f | AnalyticFractionOn U V f}
  zero_mem' := AnalyticFractionOn.const U V 0
  one_mem' := AnalyticFractionOn.const U V 1
  add_mem' hf hg := hf.add hg
  mul_mem' hf hg := hf.mul hg
  neg_mem' hf := hf.neg

def analyticFractionFunctionEval (U V : Set E) (x : E) :
    analyticFractionFunctionSubring U V →+* ℝ :=
  (Pi.evalRingHom (fun _ : E => ℝ) x).comp (analyticFractionFunctionSubring U V).subtype

@[simp] theorem analyticFractionFunctionEval_apply (U V : Set E) (x : E)
    (f : analyticFractionFunctionSubring U V) : analyticFractionFunctionEval U V x f = f.val x := rfl

end PlanarNikodym
