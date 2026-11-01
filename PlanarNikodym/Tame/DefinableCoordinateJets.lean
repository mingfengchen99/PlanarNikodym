import PlanarNikodym.Geometry.AnalyticCoordinateJets
import PlanarNikodym.Tame.DefinableCalculus

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set

namespace PlanarNikodym

/-- The higher coordinate derivatives used to resolve singular zeroes
have actual definable graphs on the original open domain. -/
theorem RanDefinableOn.coordinateJet {n : ℕ} {f : Base n → ℝ}
    {W : Set (Base n)} (hf : RanDefinableOn f W) (hW : RanDefinable W)
    (ho : IsOpen W) (ha : AnalyticOnNhd ℝ f W)
    (k : ℕ) (s : Fin k → Fin n) : RanDefinableOn (coordinateJet f k s) W := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    have hjet := ih (Fin.tail s)
    have hd := hjet.directionalDerivative hW ho
      (fun x hx => (coordinateJet_analytic ha k (Fin.tail s) x hx).differentiableAt)
      (Pi.single (s 0) 1)
    apply hd.congr
    intro x hx
    have he := coordinateJet_cons ha (Fin.tail s) (s 0) hx
    rw [Fin.cons_self_tail] at he
    exact he.symm

end PlanarNikodym
