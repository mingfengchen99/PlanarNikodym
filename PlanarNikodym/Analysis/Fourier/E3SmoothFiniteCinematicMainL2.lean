import PlanarNikodym.Analysis.Fourier.E3SmoothRetainedMovingChartMainL2
import PlanarNikodym.Analysis.Fourier.E3SmoothMovingChartGeometry
import PlanarNikodym.Analysis.Fourier.CriticalScaleThreshold

/-! The original cinematic cutoff actually produces a finite partition
whose microlocal main pieces obey uniform selected-parameter L² square
sums. All nonlinear charts, support guards, Jacobian lower bounds and
amplitude constants are constructed in the proof, rather than accepted
as an extra chart-geometry or operator input. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

theorem Family.exists_e3_finite_cinematic_main_L2_partition {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (F : FrequencyCutoff) (βfreq : ℝ → ℝ) (hβfreq : Continuous βfreq) :
    ∃ (I : Finset (tsupport χ)) (ψ : I → Cutoff d)
      (σ : I → (Fin 2 ↪ Fin (d + 2))) (ε : ℝ),
      0 < ε ∧ (∀ x, ∑ i : I, ψ i x = χ x) ∧
      ∀ i : I, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧
        tsupport (ψ i) ⊆ tsupport χ ∧
        ∃ β C M : ℝ, 0 < β ∧ 0 ≤ C ∧ 0 ≤ M ∧
          (∀ ξ : Plane, |F.bandSymbol 0 ξ * βfreq ξ.2| ≤ M) ∧
          ∀ (b δ : ℝ) (N : ℕ) (u : UnselectedCoordinates (σ i))
            (f : Plane → ℂ), Integrable f → MemLp f 2 volume →
          ∀ κ r : ℝ, 0 < κ → 0 < r → 0 < δ → δ ≤ 1 → δ ≤ ε / 2 →
          (2 * Real.pi * r) * δ ^ (2 : ℕ) ∈ Icc (0 : ℝ) 1 →
          (∀ ξ : Plane, |ξ.2| < κ → F.bandSymbol 0 ξ * βfreq ξ.2 = 0) →
          ENNReal.ofReal β * (∑ j ∈ Finset.range N, ∫⁻ z : Aux 2,
            ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff (ψ i) b δ j) F βfreq r f
              (parameterFrame d (((parameterFrame d).symm i.val.val.2 +
                selectedCoordinateSplit (σ i) (0, u)) + coordinateInsertion (σ i) z))‖ₑ ^ (2 : ℕ)) ≤
            (3 : ℝ≥0∞) * ENNReal.ofReal (C ^ (2 : ℕ) * M ^ (2 : ℕ) * κ⁻¹ * r⁻¹) *
              ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  have hm : 2 ≤ d + 2 := by omega
  obtain ⟨I, ψ, σ, E, K, L, ε, hε, hpatch, hsum⟩ :=
    G.exists_e3_smooth_movingChart_cutoff_partition hG χ hχ hc hχ0 hdet hm
  refine ⟨I, ψ, σ, ε, hε, hsum, ?_⟩
  intro i
  obtain ⟨hψ, hcψ, hsχ, _, hK, hKS, he, hea, hei,
    ⟨β, B, hβ, _hB, hJ⟩, hL, _hsL, hLift, _hreg, hspan⟩ := hpatch i
  obtain ⟨C, M, hC, hM, hsymbol, hbound⟩ :=
    G.exists_e3_uniform_movingChart_main_square_sum_bound hG hm (σ i) (E i) he hea hei
      (ψ i) hψ hK hKS hβ (fun x hx => (hJ x hx).1) (L i) hL
      ((parameterFrame d).symm i.val.val.2) hLift ε hε hspan F βfreq hβfreq
  exact ⟨hψ, hcψ, hsχ, β, C, M, hβ, hC, hM, hsymbol, hbound⟩

/-- The exact smallest time scale is available above a constructed
frequency threshold. No small-scale or geometric certificate remains
as an extra argument of this final cinematic-cutoff result. -/
theorem Family.exists_e3_finite_cinematic_critical_main_L2_partition {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (F : FrequencyCutoff) (βfreq : ℝ → ℝ) (hβfreq : Continuous βfreq) :
    ∃ (I : Finset (tsupport χ)) (ψ : I → Cutoff d)
      (σ : I → (Fin 2 ↪ Fin (d + 2))) (R : ℝ),
      1 ≤ R ∧ (∀ x, ∑ i : I, ψ i x = χ x) ∧
      ∀ i : I, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧
        tsupport (ψ i) ⊆ tsupport χ ∧
        ∃ β C M : ℝ, 0 < β ∧ 0 ≤ C ∧ 0 ≤ M ∧
          (∀ ξ : Plane, |F.bandSymbol 0 ξ * βfreq ξ.2| ≤ M) ∧
          ∀ (b : ℝ) (N : ℕ) (u : UnselectedCoordinates (σ i))
            (f : Plane → ℂ), Integrable f → MemLp f 2 volume →
          ∀ κ r : ℝ, 0 < κ → R ≤ r →
          (∀ ξ : Plane, |ξ.2| < κ → F.bandSymbol 0 ξ * βfreq ξ.2 = 0) →
          let δ := criticalTimeScale 1 (2 * Real.pi * r)
          ENNReal.ofReal β * (∑ j ∈ Finset.range N, ∫⁻ z : Aux 2,
            ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff (ψ i) b δ j) F βfreq r f
              (parameterFrame d (((parameterFrame d).symm i.val.val.2 +
                selectedCoordinateSplit (σ i) (0, u)) + coordinateInsertion (σ i) z))‖ₑ ^ (2 : ℕ)) ≤
            (3 : ℝ≥0∞) * ENNReal.ofReal (C ^ (2 : ℕ) * M ^ (2 : ℕ) * κ⁻¹ * r⁻¹) *
              ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  obtain ⟨I, ψ, σ, ε, hε, hsum, hpatch⟩ :=
    G.exists_e3_finite_cinematic_main_L2_partition hG χ hχ hc hχ0 hdet F βfreq hβfreq
  obtain ⟨R, hR, hscale⟩ := exists_Fourier_criticalTimeScale_threshold 1
    (show 0 < ε / 2 by positivity)
  refine ⟨I, ψ, σ, R, hR, hsum, ?_⟩
  intro i
  obtain ⟨hψ, hcψ, hsχ, β, C, M, hβ, hC, hM, hsymbol, hbound⟩ := hpatch i
  refine ⟨hψ, hcψ, hsχ, β, C, M, hβ, hC, hM, hsymbol, ?_⟩
  intro b N u f hf1 hf2 κ r hκ hrR hgap
  have hr : 0 < r := zero_lt_one.trans_le (hR.trans hrR)
  obtain ⟨hδ, hδbound, _heff⟩ := hscale r hrR
  have hα : (2 * Real.pi * r) * criticalTimeScale 1 (2 * Real.pi * r) ^ (2 : ℕ) ∈
      Icc (0 : ℝ) 1 := by
    rw [frequency_mul_criticalTimeScale_pow 1 (by positivity)]
    exact ⟨zero_le_one, le_rfl⟩
  exact hbound b _ N u f hf1 hf2 κ r hκ hr hδ
    (hδbound.trans (min_le_left _ _)) (hδbound.trans (min_le_right _ _)) hα hgap

end PlanarNikodym
