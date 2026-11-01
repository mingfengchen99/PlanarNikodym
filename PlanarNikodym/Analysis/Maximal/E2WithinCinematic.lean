import PlanarNikodym.Analysis.Maximal.E2SeeleyCompactClosedExtension
import PlanarNikodym.Geometry.Cinematic

/-! Cinematic jets intrinsic to the original closed time domain. Full
within Taylor tensors remove dependence on arbitrary outside values.
For an actually ambient C^(d+2) phase they agree with the existing
ambient cinematic matrix, including at the time endpoints. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def e2TimeParameterDirections (v : ℝ × E) : (n : ℕ) → Fin (n + 1) → ℝ × E
  | 0 => fun _ => v
  | n + 1 => Fin.cons (1, 0) (e2TimeParameterDirections v n)

theorem e2_timeParameterDerivative_eq_fullJet (n : ℕ)
    {f : (ℝ × E) → ℝ} {x : ℝ × E}
    (hf : ContDiffAt ℝ (n + 1) f x) (v : ℝ × E) :
    timeDerivative (fun y => fderiv ℝ f y v) n x =
      iteratedFDeriv ℝ (n + 1) f x (e2TimeParameterDirections v n) := by
  induction n generalizing x with
  | zero => simp [timeDerivative, e2TimeParameterDirections]
  | succ n ih =>
    have he : timeDerivative (fun y => fderiv ℝ f y v) n =ᶠ[𝓝 x]
        fun y => iteratedFDeriv ℝ (n + 1) f y (e2TimeParameterDirections v n) := by
      filter_upwards [hf.eventually (by simp)] with y hy
      exact ih (hy.of_le (by exact_mod_cast (Nat.le_succ (n + 1))))
    let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin (n + 1) => ℝ × E) ℝ
      (e2TimeParameterDirections v n)
    have hd := (ev.hasFDerivAt.comp x
      (hf.differentiableAt_iteratedFDeriv (by
        exact_mod_cast (Nat.lt_succ_self (n + 1)))).hasFDerivAt).fderiv
    change fderiv ℝ (timeDerivative (fun y => fderiv ℝ f y v) n) x (1, 0) = _
    rw [he.fderiv_eq]
    change fderiv ℝ (ev ∘ iteratedFDeriv ℝ (n + 1) f) x (1, 0) = _
    rw [hd, ContinuousLinearMap.comp_apply]
    change (fderiv ℝ (iteratedFDeriv ℝ (n + 1) f) x (1, 0))
      (e2TimeParameterDirections v n) = _
    rw [iteratedFDeriv_succ_apply_left]
    rfl

def Family.cinematicMatrixWithin_e2 {d : ℕ} (G : Family 2 d)
    (x : ℝ × Parameters 2 d) : Matrix (Fin (d + 2)) (Fin (d + 2)) ℝ :=
  fun i j => iteratedFDerivWithin ℝ (i.val + 1)
    (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) (G.I.carrier ×ˢ G.W) x
    (e2TimeParameterDirections (0, parameterFrame d (Pi.single j 1)) i.val)

def Family.cinematicDetWithin_e2 {d : ℕ} (G : Family 2 d)
    (x : ℝ × Parameters 2 d) : ℝ := (G.cinematicMatrixWithin_e2 x).det

theorem Family.cinematicMatrixWithin_e2_eq_ambient {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) {x : ℝ × Parameters 2 d} (hx : x ∈ G.I.carrier ×ˢ G.W)
    (hG : ContDiffAt ℝ (d + 2) (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x) :
    G.cinematicMatrixWithin_e2 x = G.cinematicMatrix x := by
  have hu : UniqueDiffOn ℝ (G.I.carrier ×ˢ G.W) :=
    (uniqueDiffOn_Icc G.I.nondegenerate).prod hW.uniqueDiffOn
  ext i j
  have hreg : ContDiffAt ℝ (i.val + 1)
      (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x :=
    hG.of_le (by exact_mod_cast (show i.val + 1 ≤ d + 2 from i.isLt))
  change iteratedFDerivWithin ℝ (i.val + 1) _ _ x _ = _
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hu hreg hx]
  exact (e2_timeParameterDerivative_eq_fullJet i.val hreg _).symm

theorem Family.cinematicDetWithin_e2_eq_ambient {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) {x : ℝ × Parameters 2 d} (hx : x ∈ G.I.carrier ×ˢ G.W)
    (hG : ContDiffAt ℝ (d + 2) (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x) :
    G.cinematicDetWithin_e2 x = G.cinematicDet x := by
  unfold cinematicDetWithin_e2 cinematicDet
  rw [G.cinematicMatrixWithin_e2_eq_ambient hW hx hG]

end PlanarNikodym
