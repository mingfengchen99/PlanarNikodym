import PlanarNikodym.Analysis.Fourier.CriticalMainLpDecay
import PlanarNikodym.Analysis.Fourier.E3SmoothFiniteCinematicMainLp

/-! The critical-time r^(-1/2) estimate for genuine C∞ cinematic data. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace PlanarNikodym

theorem Family.exists_e3_finite_cinematic_critical_main_Lp_decay_partition {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (F : FrequencyCutoff) (βfreq : ℝ → ℝ) (hβfreq : ContDiff ℝ ∞ βfreq) :
    ∃ (I : Finset (tsupport χ)) (ψ : I → Cutoff d)
      (σ : I → (Fin 2 ↪ Fin (d + 2))) (R : ℝ),
      1 ≤ R ∧ (∀ x, ∑ i : I, ψ i x = χ x) ∧
      ∀ i : I, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧
        tsupport (ψ i) ⊆ tsupport χ ∧
        ∀ p : ℝ, 2 < p → ∀ κ : ℝ, 0 < κ →
          (∀ ξ : Plane, |ξ.2| < κ → F.bandSymbol 0 ξ * βfreq ξ.2 = 0) →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ) (N : ℕ) (u : UnselectedCoordinates (σ i))
          (f : Plane → ℂ), Integrable f → MemLp f (ENNReal.ofReal p) volume →
          ∀ r : ℝ, R ≤ r →
          let δ := criticalTimeScale 1 (2 * Real.pi * r)
          eLpNorm (G.finiteSliceMain (ψ i) F βfreq r b δ N
            (fun z => parameterFrame d (((parameterFrame d).symm i.val.val.2 +
              selectedCoordinateSplit (σ i) (0, u)) + coordinateInsertion (σ i) z)) f)
            (ENNReal.ofReal p) (finiteSliceMainMeasure N) ≤
            ENNReal.ofReal (C * r ^ (-(1 / 2 : ℝ))) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨I, ψ, σ, R, hR, hsum, hpatch⟩ :=
    G.exists_e3_finite_cinematic_critical_main_Lp_partition hG χ hχ hc hχ0 hdet F βfreq hβfreq
  refine ⟨I, ψ, σ, R, hR, hsum, ?_⟩
  intro i
  obtain ⟨hψ, hcψ, hsψ, hb⟩ := hpatch i
  refine ⟨hψ, hcψ, hsψ, ?_⟩
  intro p hp κ hκ hgap
  obtain ⟨C, hC, hbound⟩ := hb p hp
  let D := (2 * Real.pi * C * κ⁻¹) ^ (1 / p) * (2 * Real.pi) ^ (-(1 / 2 : ℝ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro b N u f hf hfp r hr
  have hrpos : 0 < r := zero_lt_one.trans_le (hR.trans hr)
  have hbnd := hbound b N u f hf hfp κ r hκ hr hgap
  dsimp only at hbnd ⊢
  rw [critical_main_interpolation_scale_eq hC hκ hrpos (by linarith : 0 < p)] at hbnd
  exact hbnd


end PlanarNikodym
