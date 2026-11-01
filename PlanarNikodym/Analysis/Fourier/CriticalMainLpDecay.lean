import PlanarNikodym.Analysis.Fourier.FiniteCinematicMainLp

/-! Exact critical-scale simplification and the readable r^(-1/2)
smallest-piece Lp endpoint for the actual cinematic main term. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace PlanarNikodym

/-- On the exact smallest time scale the interpolated factor is a
constant times r^(-1/2), independently of the exponent p. -/
theorem critical_main_interpolation_scale_eq
    {C κ r p : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ) (hr : 0 < r) (hp : 0 < p) :
    (C * κ⁻¹ * r⁻¹ * (criticalTimeScale 1 (2 * Real.pi * r)) ^ (p - 2)) ^ (1 / p) =
      ((2 * Real.pi * C * κ⁻¹) ^ (1 / p) * (2 * Real.pi) ^ (-(1 / 2 : ℝ))) *
        r ^ (-(1 / 2 : ℝ)) := by
  let δ := criticalTimeScale 1 (2 * Real.pi * r)
  have hδ : 0 < δ := criticalTimeScale_pos 1 (by positivity)
  have hfreq : (2 * Real.pi * r) * δ ^ (2 : ℕ) = 1 :=
    frequency_mul_criticalTimeScale_pow 1 (by positivity)
  have hri : r⁻¹ = 2 * Real.pi * δ ^ (2 : ℕ) := by
    calc
      r⁻¹ = r⁻¹ * ((2 * Real.pi * r) * δ ^ (2 : ℕ)) := by rw [hfreq, mul_one]
      _ = _ := by field_simp [hr.ne']
  have hpow : δ ^ (2 : ℕ) * δ ^ (p - 2) = δ ^ p := by
    rw [← Real.rpow_natCast δ 2, ← Real.rpow_add hδ]
    congr 1
    ring
  have hcoef : C * κ⁻¹ * r⁻¹ * δ ^ (p - 2) =
      (2 * Real.pi * C * κ⁻¹) * δ ^ p := by
    rw [hri]
    calc
      _ = (2 * Real.pi * C * κ⁻¹) * (δ ^ (2 : ℕ) * δ ^ (p - 2)) := by ring
      _ = _ := by rw [hpow]
  change (C * κ⁻¹ * r⁻¹ * δ ^ (p - 2)) ^ (1 / p) = _
  rw [hcoef, Real.mul_rpow (by positivity) (Real.rpow_nonneg hδ.le _),
    ← Real.rpow_mul hδ.le, mul_one_div_cancel hp.ne', Real.rpow_one]
  have hd : δ = (2 * Real.pi) ^ (-(1 / 2 : ℝ)) * r ^ (-(1 / 2 : ℝ)) := by
    dsimp [δ, criticalTimeScale]
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [Real.mul_rpow (by positivity) hr.le]
  rw [hd]
  ring

/-- Readable smallest-piece endpoint: for a fixed frequency gap, every
p>2 has a uniform r^(-1/2) bound on the finite family of actual main pieces. -/
theorem Family.exists_finite_cinematic_critical_main_Lp_decay_partition {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (ha : ∀ x ∈ tsupport χ, AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
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
    G.exists_finite_cinematic_critical_main_Lp_partition χ hχ hc hχ0 ha hdet F βfreq hβfreq
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
