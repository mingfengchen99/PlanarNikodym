import PlanarNikodym.Analysis.Fourier.UniformInverseChartConeL2

/-! The actual locally smooth phase enters the constructed uniform cone
amplitude estimate through a genuine global extension, which preserves
the full Taylor correction at the original center and endpoint. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

theorem exists_uniform_local_inverseChart_amplitude_cone_bound {d : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2))
    (hi : AnalyticOnNhd ℝ e.symm e.target) (σ : Fin 2 ↪ Fin (d + 2))
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    (Φ : Parameters 2 d × ℝ → ℝ)
    {L U : Set (Parameters 2 d × ℝ)} (hL : IsCompact L) (hU : IsOpen U)
    (hLU : L ⊆ U) (hΦ : ∀ x ∈ U, ContDiffAt ℝ ∞ Φ x)
    {K : Set ((ℝ × Aux (d + 2)) × Aux 2)} (hK : IsCompact K) (hKT : K ⊆ e.target)
    {J : Set ℝ} (hJ : IsCompact J) :
    ∃ (S : LinearAmplitudeParameters d → SchwartzMap (Plane × Plane) ℂ) (C : ℝ),
      0 ≤ C ∧
      (∀ q y, (q, y) ∈ K → ∀ (r δ τ : ℝ) (η : ℝ), η ∈ J →
        r * δ ^ (2 : ℕ) ∈ Icc (0 : ℝ) 1 → δ ∈ Icc (0 : ℝ) 1 →
        let p := parameterFrame d (q.2 + coordinateInsertion σ (e.symm (q, y)).2)
        (a (p, q.1 + δ * τ, η) * (timePartitionWindow τ : ℂ) ≠ 0 →
          (p, q.1) ∈ L ∧ (p, q.1 + δ * τ) ∈ L) →
        S (q, (r * δ ^ (2 : ℕ), δ)) ((y 0, y 1), (τ, η)) =
          actualTaylorAmplitude a Φ 1 r q.1 δ p τ η) ∧
      (∀ p w x, timePartitionWindow x.1 = 0 → S p (w, x) = 0) ∧
      (∀ p, (∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier (S p) ζ‖ₑ) ≤
        ENNReal.ofReal C) ∧
      ∀ p (h : Plane → ℂ), Measurable h → Integrable h → MemLp h 2 volume →
        ∀ κ r δ : ℝ, 0 < κ → 0 < r → 0 < δ →
        (∀ x : Plane, |x.2| < κ → h x = 0) →
        eLpNorm (dilatedAmplitudeConeExtension (fun w x => S p (w, x)) h r δ) 2 volume ≤
          ENNReal.ofReal C * ENNReal.ofReal δ⁻¹ ^ (1 / (2 : ℝ)) *
            ENNReal.ofReal (κ⁻¹ * r⁻¹ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) * eLpNorm h 2 volume := by
  obtain ⟨Ψ, hΨ, _, hlocal⟩ := exists_local_smooth_Taylor_amplitude Φ hL hU hLU hΦ
  obtain ⟨S, C, hC, hmatch, hzero, hcoef, hbound⟩ :=
    exists_uniform_inverseChart_amplitude_cone_bound e hi σ ha hΨ hK hKT hJ
  refine ⟨S, C, hC, ?_, hzero, hcoef, hbound⟩
  intro q y hqy r δ τ η hη hα hδ p hguard
  rw [uniformInverseChart_amplitude_eq_actual e σ a hΨ S hmatch hqy r δ τ hη hα hδ]
  by_cases hz : a (p, q.1 + δ * τ, η) * (timePartitionWindow τ : ℂ) = 0
  · change (a (p, q.1 + δ * τ, η) * (timePartitionWindow τ : ℂ)) * _ =
      (a (p, q.1 + δ * τ, η) * (timePartitionWindow τ : ℂ)) * _
    simp only [hz, zero_mul]
  · obtain ⟨hp0, hp1⟩ := hguard hz
    exact ((hlocal a 1 p r q.1 δ τ η hp0 hp1).trans
      (rescaledTaylorAmplitude_eq_actualTaylorAmplitude a hΨ 1 p r q.1 δ τ η)).symm

end PlanarNikodym
