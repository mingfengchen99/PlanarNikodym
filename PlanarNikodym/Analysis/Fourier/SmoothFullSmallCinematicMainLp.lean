import PlanarNikodym.Analysis.Fourier.SmoothSmallCinematicMainL2Norm
import PlanarNikodym.Analysis.Fourier.FullSmallCinematicMainLp

/-! Genuine C-infinity estimates, including zero auxiliary dimension. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators ComplexConjugate
namespace PlanarNikodym

theorem Family.exists_smooth_finite_cinematic_small_main_Lp_norm_partition {d : ℕ}
    (G : Family 2 d) (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)

    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (F : FrequencyCutoff) (βfreq : ℝ → ℝ) (hβfreq : ContDiff ℝ ∞ βfreq)
    (p : ℝ≥0) (hp : 2 ≤ p) :
    ∃ (I : Finset (tsupport χ)) (ψ : I → Cutoff d)
      (σ : I → (Fin 2 ↪ Fin (d + 2))) (ε : ℝ),
      0 < ε ∧ (∀ x, ∑ i : I, ψ i x = χ x) ∧
      ∀ i : I, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧
        tsupport (ψ i) ⊆ tsupport χ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ (b δ : ℝ) (N : ℕ) (u : UnselectedCoordinates (σ i)) (f : Plane → ℂ),
          Integrable f → MemLp f p volume →
          ∀ κ r : ℝ, 0 < κ → 0 < r → 0 < δ → δ ≤ 1 → δ ≤ ε / 2 →
          (2 * Real.pi * r) * δ ^ (2 : ℕ) ∈ Icc (0 : ℝ) 1 →
          (∀ ξ : Plane, |ξ.2| < κ → F.bandSymbol 0 ξ * βfreq ξ.2 = 0) →
          eLpNorm (G.finiteSliceMain (ψ i) F βfreq r b δ N
            (fun z => parameterFrame d (((parameterFrame d).symm i.val.val.2 +
              selectedCoordinateSplit (σ i) (0, u)) + coordinateInsertion (σ i) z)) f)
            p (finiteSliceMainMeasure N) ≤
            ENNReal.ofReal ((C * κ⁻¹ * r⁻¹ * δ ^ ((p : ℝ) - 2)) ^ (1 / (p : ℝ))) *
              eLpNorm f p volume := by
  rcases eq_or_lt_of_le hp with he | hlt
  · subst p
    obtain ⟨I, ψ, σ, ε, hε, hs, hb⟩ :=
      G.exists_smooth_finite_cinematic_small_main_L2_norm_partition hG χ hχ hc hχ0 hdet F βfreq hβfreq.continuous
    refine ⟨I, ψ, σ, ε, hε, hs, ?_⟩
    intro i
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, sub_self, Real.rpow_zero, mul_one] using hb i
  · obtain ⟨I, ψ, σ, ε, hε, hs, hb⟩ :=
      G.exists_smooth_finite_cinematic_small_main_Lp_partition hG χ hχ hc hχ0 hdet F βfreq hβfreq
    refine ⟨I, ψ, σ, ε, hε, hs, ?_⟩
    intro i
    refine ⟨(hb i).1, (hb i).2.1, (hb i).2.2.1, ?_⟩
    simpa only [ENNReal.ofReal_coe_nnreal] using (hb i).2.2.2 (p : ℝ) (by exact_mod_cast hlt)

/-- Whole-parameter estimate for actual finite families of smallest or
finer time pieces. The original cutoff is reconstructed exactly; the
fixed coefficient is independent of the number of pieces, translation,
time scale, frequency, input and the positive frequency gap κ. -/
theorem Family.exists_smooth_full_cinematic_small_main_Lp {d : ℕ}
    (G : Family 2 d) (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)

    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (F : FrequencyCutoff) (βfreq : ℝ → ℝ) (hβfreq : ContDiff ℝ ∞ βfreq)
    {p : ℝ≥0} (hp : 2 ≤ p) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ (b δ : ℝ) (N : ℕ) (f : Plane → ℂ),
      Integrable f → MemLp f p volume → ∀ κ r : ℝ,
      0 < κ → 0 < r → 0 < δ → δ ≤ 1 → δ ≤ ε / 2 →
      (2 * Real.pi * r) * δ ^ (2 : ℕ) ∈ Icc (0 : ℝ) 1 →
      (∀ ξ : Plane, |ξ.2| < κ → F.bandSymbol 0 ξ * βfreq ξ.2 = 0) →
      eLpNorm (G.fullFiniteSliceMain χ F βfreq r b δ N f) p
        (fullFiniteSliceMainMeasure d N) ≤
        ENNReal.ofReal (C * (κ⁻¹ * r⁻¹ * δ ^ ((p : ℝ) - 2)) ^ (1 / (p : ℝ))) *
          eLpNorm f p volume := by
  classical
  obtain ⟨I, ψ, σ, ε, hε, hsum, hpatch⟩ :=
    G.exists_smooth_finite_cinematic_small_main_Lp_norm_partition hG χ hχ hc hχ0 hdet F βfreq hβfreq p hp
  have hp0 : 0 < p := (by norm_num : (0 : ℝ≥0) < 2).trans_le hp
  have hlocal (i : I) := (hpatch i).2.2.2
  choose C hC hb using hlocal
  have hvolume (i : I) := exists_full_finite_fiber_norm_factor (σ i)
    ((parameterFrame d).symm i.val.val.2) (tsupport (ψ i)) (hpatch i).2.1
  choose V hV hv using hvolume
  let A := fun i : I => V i ^ (1 / (p : ℝ)) * (C i) ^ (1 / (p : ℝ))
  have hA (i : I) : 0 ≤ A i := mul_nonneg (Real.rpow_nonneg (hV i).le _) (Real.rpow_nonneg (hC i) _)
  refine ⟨∑ i, A i, ε, Finset.sum_nonneg (fun i _ => hA i), hε, ?_⟩
  intro b δ N f hf hfp κ r hκ hr hδ hδ1 hδε hα hgap
  let B := (κ⁻¹ * r⁻¹ * δ ^ ((p : ℝ) - 2)) ^ (1 / (p : ℝ))
  have hB : 0 ≤ B := Real.rpow_nonneg (by positivity) _
  let H := fun i : I => G.fullFiniteSliceMain (ψ i) F βfreq r b δ N f
  have hm (i : I) : Measurable (H i) := G.e3_measurable_fullFiniteSliceMain hG (ψ i)
    (hpatch i).1.continuous (hpatch i).2.1 F βfreq hβfreq.continuous r b δ N hf
  have hi (i : I) : eLpNorm (H i) p (fullFiniteSliceMainMeasure d N) ≤
      ENNReal.ofReal (A i * B) * eLpNorm f p volume := by
    have hbf (u : UnselectedCoordinates (σ i)) :
        eLpNorm (fun w : Fin N × Aux 2 =>
          H i (w.1, glyzFiberParameter (σ i) ((parameterFrame d).symm i.val.val.2) u w.2))
            p (finiteSliceMainMeasure N) ≤
          ENNReal.ofReal ((C i) ^ (1 / (p : ℝ)) * B) * eLpNorm f p volume := by
      have hh := hb i b δ N u f hf hfp κ r hκ hr hδ hδ1 hδε hα hgap
      have he : (C i * κ⁻¹ * r⁻¹ * δ ^ ((p : ℝ) - 2)) ^ (1 / (p : ℝ)) =
          (C i) ^ (1 / (p : ℝ)) * B := by
        rw [show C i * κ⁻¹ * r⁻¹ * δ ^ ((p : ℝ) - 2) =
          C i * (κ⁻¹ * r⁻¹ * δ ^ ((p : ℝ) - 2)) by ring,
          Real.mul_rpow (hC i) (by positivity)]
      rw [he] at hh
      unfold Family.finiteSliceMain at hh
      simpa only [H, Family.fullFiniteSliceMain, glyzFiberParameter, glyzFiberBase] using hh
    have hh := hv i N (H i) (hm i)
      (G.fullFiniteSliceMain_support (ψ i) F βfreq r b δ N f) p hp0
      (ENNReal.ofReal ((C i) ^ (1 / (p : ℝ)) * B) * eLpNorm f p volume) hbf
    apply hh.trans_eq
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hV i).le _)]
    congr 2
    dsimp only [A]
    ring
  rw [G.fullFiniteSliceMain_sum_cutoff χ ψ (fun i => (hpatch i).1)
    (fun i => (hpatch i).2.1)
    (fun _ _ _ => hG.continuous.continuousAt)
    hsum F βfreq hβfreq.continuous r b δ N hf]
  calc
    _ ≤ ∑ i : I, eLpNorm (H i) p (fullFiniteSliceMainMeasure d N) :=
      eLpNorm_sum_le (fun i _ => (hm i).aestronglyMeasurable)
        (by exact_mod_cast (show (1 : ℝ≥0) ≤ p from (by norm_num : (1 : ℝ≥0) ≤ 2).trans hp))
    _ ≤ ∑ i : I, ENNReal.ofReal (A i * B) * eLpNorm f p volume :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
        (fun i _ => mul_nonneg (hA i) hB), ← Finset.sum_mul]

end PlanarNikodym
