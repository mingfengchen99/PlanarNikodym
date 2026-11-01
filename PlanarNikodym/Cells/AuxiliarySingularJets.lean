import PlanarNikodym.Geometry.AnalyticFiniteOrder
import PlanarNikodym.Cells.AnalyticFiberExceptions

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology

namespace PlanarNikodym

def auxiliaryJet {d : ℕ} (f : Parameters 2 d → ℝ) (k : ℕ)
    (s : Fin k → Fin d) (p : Parameters 2 d) : ℝ :=
  coordinateJet (fun u => f (p.1, u)) k s p.2

@[simp] theorem auxiliaryJet_zero {d : ℕ} (f : Parameters 2 d → ℝ)
    (s : Fin 0 → Fin d) (p : Parameters 2 d) : auxiliaryJet f 0 s p = f p := rfl

theorem analytic_auxiliary_slice {d : ℕ} {f : Parameters 2 d → ℝ}
    {W : Set (Parameters 2 d)} (ha : AnalyticOnNhd ℝ f W) (z : Base 2) :
    AnalyticOnNhd ℝ (fun u => f (z, u)) {u | (z, u) ∈ W} := by
  intro u hu
  exact (ha (z, u) hu).comp (f := fun u => (z, u))
    (analyticAt_const.prod analyticAt_id)

/-- The slice definition agrees with the joint derivative in a purely
auxiliary direction; no centre direction enters the formula. -/
theorem auxiliaryJet_cons_of_differentiable {d k : ℕ}
    {f : Parameters 2 d → ℝ} {W : Set (Parameters 2 d)}
    (ha : AnalyticOnNhd ℝ f W) (s : Fin k → Fin d) (j : Fin d)
    {p : Parameters 2 d} (hp : p ∈ W)
    (hd : DifferentiableAt ℝ (auxiliaryJet f k s) p) :
    auxiliaryJet f (k + 1) (Fin.cons j s) p =
      fderiv ℝ (auxiliaryJet f k s) p (0, Pi.single j 1) := by
  have he := coordinateJet_cons (analytic_auxiliary_slice ha p.1) s j hp
  change auxiliaryJet f (k + 1) (Fin.cons j s) p =
    fderiv ℝ (fun u => auxiliaryJet f k s (p.1, u)) p.2 (Pi.single j 1) at he
  rw [he, fderiv_snd_slice (auxiliaryJet f k s) p hd]
  rfl

theorem auxiliaryJet_analytic {d : ℕ} {f : Parameters 2 d → ℝ}
    {W : Set (Parameters 2 d)} (ho : IsOpen W) (ha : AnalyticOnNhd ℝ f W)
    (k : ℕ) (s : Fin k → Fin d) : AnalyticOnNhd ℝ (auxiliaryJet f k s) W := by
  induction k with
  | zero => exact ha
  | succ k ih =>
    have hprev := ih (Fin.tail s)
    intro p hp
    have hA : AnalyticAt ℝ
        (fun q => fderiv ℝ (auxiliaryJet f k (Fin.tail s)) q
          (0, Pi.single (s 0) 1)) p :=
      ((ContinuousLinearMap.apply ℝ ℝ ((0, Pi.single (s 0) 1) : Parameters 2 d)).analyticAt _).comp
        (hprev p hp).fderiv
    apply hA.congr
    filter_upwards [ho.mem_nhds hp] with q hq
    have he := auxiliaryJet_cons_of_differentiable ha (Fin.tail s) (s 0) hq
      (hprev q hq).differentiableAt
    rw [Fin.cons_self_tail] at he
    exact he.symm

/-- Every auxiliary-singular zero either lies over a locally flat fibre
or has an actual higher auxiliary jet with a regular auxiliary zero.
Thus singularity of the original first derivative is not a stopping
condition for the local dimension-drop construction. -/
theorem auxiliary_zero_flat_or_regularJet {d : ℕ}
    {f : Parameters 2 d → ℝ} {W : Set (Parameters 2 d)}
    (ho : IsOpen W) (ha : AnalyticOnNhd ℝ f W)
    {p : Parameters 2 d} (hp : p ∈ W) (hfp : f p = 0) :
    (∀ᶠ u in 𝓝 p.2, f (p.1, u) = 0) ∨
      ∃ (k : ℕ) (s : Fin k → Fin d) (j : Fin d),
        auxiliaryJet f k s p = 0 ∧
          fderiv ℝ (auxiliaryJet f k s) p (0, Pi.single j 1) ≠ 0 := by
  classical
  by_cases hflat : ∀ᶠ u in 𝓝 p.2, f (p.1, u) = 0
  · exact Or.inl hflat
  · apply Or.inr
    have hex : ∃ (k : ℕ) (s : Fin k → Fin d), auxiliaryJet f k s p ≠ 0 := by
      by_contra! hzero
      exact hflat (analytic_eventually_zero_of_coordinateJets_zero
        (analytic_auxiliary_slice ha p.1 p.2 hp) hzero)
    let P (k : ℕ) := ∃ s : Fin k → Fin d, auxiliaryJet f k s p ≠ 0
    have hP : ∃ k, P k := hex
    have hkpos : 0 < Nat.find hP := by
      by_contra hn
      have hkzero : Nat.find hP = 0 := by omega
      have hz : P 0 := hkzero ▸ Nat.find_spec hP
      obtain ⟨s, hs⟩ := hz
      exact hs hfp
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
    have hsucc : P (Nat.find hP) := Nat.find_spec hP
    rw [hk] at hsucc
    obtain ⟨s, hs⟩ := hsucc
    have hlow : auxiliaryJet f k (Fin.tail s) p = 0 := by
      by_contra hn
      have hmin := Nat.find_min' hP (show P k from ⟨Fin.tail s, hn⟩)
      omega
    refine ⟨k, Fin.tail s, s 0, hlow, ?_⟩
    have he := auxiliaryJet_cons_of_differentiable ha (Fin.tail s) (s 0) hp
      (auxiliaryJet_analytic ho ha k (Fin.tail s) p hp).differentiableAt
    rw [Fin.cons_self_tail] at he
    exact he ▸ hs

end PlanarNikodym
