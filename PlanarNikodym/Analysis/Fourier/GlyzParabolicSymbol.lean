import PlanarNikodym.Analysis.Fourier.InverseChartAmplitude
import PlanarNikodym.Analysis.Fourier.LocalComplexAmplitudeExtension
import PlanarNikodym.Analysis.Fourier.TimeSliceExtension
import PlanarNikodym.Analysis.Fourier.GlyzCompactPhaseExtension

/-! Compact inverse-jet symbols in every Taylor degree. The amplitude
and the real normalized remainder are extended separately, retaining
all values of the frequency-weighted remainder parameter α. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace PlanarNikodym

abbrev GlyzParabolicSymbolVariables (d n : ℕ) := CinematicAmplitudeVariables d n × ℝ

def glyzInverseChartBaseSymbol {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (σ : Fin (n + 1) ↪ Fin (d + 2)) (a : Parameters 2 d × ℝ × ℝ → ℂ)
    (z : GlyzParabolicSymbolVariables d n) : ℂ :=
  a (parameterFrame d (z.1.1.1.2 + coordinateInsertion σ (e.symm z.1.1).2),
    z.1.1.1.1 + z.2 * z.1.2.1, z.1.2.2) * (timePartitionWindow z.1.2.1 : ℂ)

def glyzInverseChartRemainderProfile {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (σ : Fin (n + 1) ↪ Fin (d + 2)) (Φ : Parameters 2 d × ℝ → ℝ)
    (z : GlyzParabolicSymbolVariables d n) : ℝ :=
  z.1.2.2 * z.1.2.1 ^ (n + 1) * timeTaylorIntegralRemainder Φ n
    (parameterFrame d (z.1.1.1.2 + coordinateInsertion σ (e.symm z.1.1).2),
      z.1.1.1.1, z.2 * z.1.2.1)

theorem inverseChartTaylorAmplitude_eq_base_mul_profile {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (σ : Fin (n + 1) ↪ Fin (d + 2)) (a : Parameters 2 d × ℝ × ℝ → ℂ)
    (Φ : Parameters 2 d × ℝ → ℝ) (x : CinematicAmplitudeVariables d n) (α δ : ℝ) :
    inverseChartTaylorAmplitude e σ a Φ (x, α, δ) =
      glyzInverseChartBaseSymbol e σ a (x, δ) *
        Complex.exp (((α * glyzInverseChartRemainderProfile e σ Φ (x, δ) : ℝ) : ℂ) * Complex.I) := by
  unfold inverseChartTaylorAmplitude rescaledTaylorAmplitude glyzInverseChartBaseSymbol
    taylorPhaseCorrection scaledTimeTaylorErrorProfile glyzInverseChartRemainderProfile
  congr 3
  push_cast
  ring

theorem contDiffAt_glyzInverseChartBaseSymbol {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (σ : Fin (n + 1) ↪ Fin (d + 2))
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    (z : GlyzParabolicSymbolVariables d n) (hi : ContDiffAt ℝ ∞ e.symm z.1.1) :
    ContDiffAt ℝ ∞ (glyzInverseChartBaseSymbol e σ a) z := by
  have hei : ContDiffAt ℝ ∞ (fun y : GlyzParabolicSymbolVariables d n => e.symm y.1.1) z :=
    hi.comp z contDiffAt_fst.fst
  have hp : ContDiffAt ℝ ∞ (fun y : GlyzParabolicSymbolVariables d n =>
      parameterFrame d (y.1.1.1.2 + coordinateInsertion σ (e.symm y.1.1).2)) z :=
    (parameterFrame d).contDiff.contDiffAt.comp z
      (contDiffAt_fst.fst.fst.snd.add ((coordinateInsertion σ).contDiff.contDiffAt.comp z hei.snd))
  exact (ha.contDiffAt.comp z
    (hp.prodMk ((contDiffAt_fst.fst.fst.fst.add (contDiffAt_snd.mul contDiffAt_fst.snd.fst)).prodMk
      contDiffAt_fst.snd.snd))).mul
    ((Complex.ofRealCLM.contDiff.comp contDiff_timePartitionWindow).contDiffAt.comp z
      contDiffAt_fst.snd.fst)

theorem contDiffAt_glyzInverseChartRemainderProfile {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (σ : Fin (n + 1) ↪ Fin (d + 2))
    {Φ : Parameters 2 d × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (z : GlyzParabolicSymbolVariables d n) (hi : ContDiffAt ℝ ∞ e.symm z.1.1) :
    ContDiffAt ℝ ∞ (glyzInverseChartRemainderProfile e σ Φ) z := by
  have hei : ContDiffAt ℝ ∞ (fun y : GlyzParabolicSymbolVariables d n => e.symm y.1.1) z :=
    hi.comp z contDiffAt_fst.fst
  have hp : ContDiffAt ℝ ∞ (fun y : GlyzParabolicSymbolVariables d n =>
      parameterFrame d (y.1.1.1.2 + coordinateInsertion σ (e.symm y.1.1).2)) z :=
    (parameterFrame d).contDiff.contDiffAt.comp z
      (contDiffAt_fst.fst.fst.snd.add ((coordinateInsertion σ).contDiff.contDiffAt.comp z hei.snd))
  exact (contDiffAt_fst.snd.snd.mul (contDiffAt_fst.snd.fst.pow (n + 1))).mul
    ((contDiff_timeTaylorIntegralRemainder hΦ n).contDiffAt.comp z
      (hp.prodMk (contDiffAt_fst.fst.fst.fst.prodMk (contDiffAt_snd.mul contDiffAt_fst.snd.fst))))

/-- The two compact functions are chosen before α, including α>1.
All Taylor error remains in their exact oscillatory product. -/
theorem exists_glyz_compact_parabolic_symbols {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (hi : ∀ x ∈ e.target, ContDiffAt ℝ ∞ e.symm x) (σ : Fin (n + 1) ↪ Fin (d + 2))
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : Parameters 2 d × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set ((ℝ × Aux (d + 2)) × Aux (n + 1))} (hK : IsCompact K) (hKT : K ⊆ e.target)
    {J : Set ℝ} (hJ : IsCompact J) :
    ∃ (A : GlyzParabolicSymbolVariables d n → ℂ) (H : GlyzParabolicSymbolVariables d n → ℝ),
      ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧ ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      (∀ q y, (q, y) ∈ K → ∀ τ : ℝ, ∀ η ∈ J, ∀ δ ∈ Icc (0 : ℝ) 1, ∀ α : ℝ,
        A (((q, y), (τ, η)), δ) * Complex.exp
          (((α * H (((q, y), (τ, η)), δ) : ℝ) : ℂ) * Complex.I) =
            inverseChartTaylorAmplitude e σ a Φ ((((q, y), (τ, η)), α, δ))) ∧
      (∀ z, timePartitionWindow z.1.2.1 = 0 → A z = 0) := by
  let W : Set (GlyzParabolicSymbolVariables d n) :=
    (K ×ˢ (Icc (-1 : ℝ) 1 ×ˢ J)) ×ˢ Icc (0 : ℝ) 1
  have hW : IsCompact W := (hK.prod (isCompact_Icc.prod hJ)).prod isCompact_Icc
  let U : Set (GlyzParabolicSymbolVariables d n) := {z | z.1.1 ∈ e.target}
  have hU : IsOpen U := e.open_target.preimage (by fun_prop)
  have hWU : W ⊆ U := fun _ hz => hKT hz.1.1
  obtain ⟨A, NA, hA, hcA, _hNA, hWNA, _hNAU, hNA, hAz⟩ :=
    exists_compact_smooth_complex_extension (glyzInverseChartBaseSymbol e σ a) hW hU hWU
      (fun z hz => contDiffAt_glyzInverseChartBaseSymbol e σ ha z (hi _ hz))
  obtain ⟨H, NH, hH, hcH, _hNH, hWNH, _hNHU, hNH⟩ :=
    exists_compact_smooth_extension (glyzInverseChartRemainderProfile e σ Φ) hW hU hWU
      (fun z hz => contDiffAt_glyzInverseChartRemainderProfile e σ hΦ z (hi _ hz))
  have hzero (z : GlyzParabolicSymbolVariables d n) (hz : timePartitionWindow z.1.2.1 = 0) :
      glyzInverseChartBaseSymbol e σ a z = 0 := by
    simp only [glyzInverseChartBaseSymbol, hz, Complex.ofReal_zero, mul_zero]
  refine ⟨A, H, hA, hcA, hH, hcH, ?_, fun z hz => hAz z (hzero z hz)⟩
  intro q y hqy τ η hη δ hδ α
  rw [inverseChartTaylorAmplitude_eq_base_mul_profile]
  by_cases hτ : τ ∈ Icc (-1 : ℝ) 1
  · have hz : (((q, y), (τ, η)), δ) ∈ W := ⟨⟨hqy, hτ, hη⟩, hδ⟩
    rw [hNA (hWNA hz), hNH (hWNH hz)]
  · have hw : timePartitionWindow τ = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hmem => hτ (tsupport_timePartitionWindow_subset hmem))
    have hz := hzero (((q, y), (τ, η)), δ) hw
    rw [hAz _ hz, hz, zero_mul, zero_mul]

/-- A chart-supported version with a global exact cutoff identity.
In particular, the extension never contributes outside the actual chart. -/
theorem exists_glyz_supported_parabolic_symbols {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (hi : ∀ x ∈ e.target, ContDiffAt ℝ ∞ e.symm x) (σ : Fin (n + 1) ↪ Fin (d + 2))
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : Parameters 2 d × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set ((ℝ × Aux (d + 2)) × Aux (n + 1))} (hK : IsCompact K) (hKT : K ⊆ e.target)
    {J : Set ℝ} (hJ : IsCompact J) :
    ∃ (ρ : GlyzParabolicSymbolVariables d n → ℝ)
      (A : GlyzParabolicSymbolVariables d n → ℂ) (H : GlyzParabolicSymbolVariables d n → ℝ),
      ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ (∀ z, 0 ≤ ρ z ∧ ρ z ≤ 1) ∧
      (∀ q y, (q, y) ∈ K → ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ η ∈ J,
        ∀ δ ∈ Icc (0 : ℝ) 1, ρ (((q, y), (τ, η)), δ) = 1) ∧
      tsupport ρ ⊆ {z | z.1.1 ∈ e.target} ∧
      ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧ tsupport A ⊆ {z | z.1.1 ∈ e.target} ∧
      ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ {z | z.1.1 ∈ e.target} ∧
      (∀ z, A z = (ρ z : ℂ) * glyzInverseChartBaseSymbol e σ a z) ∧
      ∀ z α, A z * Complex.exp (((α * H z : ℝ) : ℂ) * Complex.I) =
        (ρ z : ℂ) * inverseChartTaylorAmplitude e σ a Φ (z.1, α, z.2) := by
  let W : Set (GlyzParabolicSymbolVariables d n) :=
    (K ×ˢ (Icc (-1 : ℝ) 1 ×ˢ J)) ×ˢ Icc (0 : ℝ) 1
  have hW : IsCompact W := (hK.prod (isCompact_Icc.prod hJ)).prod isCompact_Icc
  let U : Set (GlyzParabolicSymbolVariables d n) := {z | z.1.1 ∈ e.target}
  have hU : IsOpen U := e.open_target.preimage (by fun_prop)
  have hWU : W ⊆ U := fun _ hz => hKT hz.1.1
  obtain ⟨ρ, A, H, hρ, hcρ, hrange, hρ1, hρU, hA, hcA, hAU, hH, hcH, hHU, hAe, heq⟩ :=
    exists_glyz_compact_phase_amplitude (glyzInverseChartBaseSymbol e σ a)
      (glyzInverseChartRemainderProfile e σ Φ) hW hU hWU
      (fun z hz => contDiffAt_glyzInverseChartBaseSymbol e σ ha z (hi _ hz))
      (fun z hz => contDiffAt_glyzInverseChartRemainderProfile e σ hΦ z (hi _ hz))
  refine ⟨ρ, A, H, hρ, hcρ, hrange, ?_, hρU, hA, hcA, hAU, hH, hcH, hHU, hAe, ?_⟩
  · intro q y hqy τ hτ η hη δ hδ
    exact hρ1 _ ⟨⟨hqy, hτ, hη⟩, hδ⟩
  · intro z α
    rw [inverseChartTaylorAmplitude_eq_base_mul_profile]
    exact heq z α

/-- Compact joint functions have globally uniform full fiber jets. -/
theorem exists_glyz_uniform_compact_fiber_jets
    {E Q F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E × Q → F) (hB : ContDiff ℝ ∞ B) (hcB : HasCompactSupport B) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q x, ‖iteratedFDeriv ℝ j (fun y => B (y, q)) x‖ ≤ C := by
  let T := fun y : E × Q => iteratedFDeriv ℝ j (fun x => B (x, y.2)) y.1
  have hT : Continuous T := continuous_iff_continuousAt.mpr fun y =>
    (contDiffAt_fiber_iteratedFDeriv j (hB.contDiffAt (x := y))).continuousAt
  have hcT : HasCompactSupport T := by
    apply HasCompactSupport.intro hcB.isCompact
    intro y hy
    have hz : (fun x : E => B (x, y.2)) =ᶠ[𝓝 y.1] 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hy).comp_tendsto
        (continuous_id.prodMk continuous_const).continuousAt
    simpa only [Pi.zero_def, iteratedFDeriv_fun_zero] using (hz.iteratedFDeriv ℝ j).self_of_nhds
  obtain ⟨y₀, hy₀⟩ := hT.norm.exists_forall_ge_of_hasCompactSupport hcT.norm
  exact ⟨‖T y₀‖, norm_nonneg _, fun q x => hy₀ (x, q)⟩

/-- The inverse anisotropic scaling does not increase any mixed jet.
The uniform constants cover the expanding rescaled output domains. -/
theorem exists_glyz_uniform_parabolic_symbol_jets {d n : ℕ} {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : GlyzParabolicSymbolVariables d n → F)
    (hB : ContDiff ℝ ∞ B) (hcB : HasCompactSupport B) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
      ∀ x : CinematicAmplitudeVariables d n,
        ‖iteratedFDeriv ℝ j (fun y => B
          (inverseCoefficientVariables (ℝ × Aux (d + 2)) n δ hδ.ne' y, δ)) x‖ ≤ C := by
  obtain ⟨C, hC, hjet⟩ := exists_glyz_uniform_compact_fiber_jets B hB hcB j
  refine ⟨C, hC, fun δ hδ hδ1 x => ?_⟩
  exact (norm_iteratedFDeriv_comp_contraction_equiv
    (inverseCoefficientVariables (ℝ × Aux (d + 2)) n δ hδ.ne')
    (norm_inverseCoefficientVariables_le_one n hδ hδ1)
    (fun y => B (y, δ)) j x).trans (hjet δ _)

end PlanarNikodym
