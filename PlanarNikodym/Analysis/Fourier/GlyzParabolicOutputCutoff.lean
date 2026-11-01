import PlanarNikodym.Analysis.Fourier.GlyzParabolicRescaling

/-! Output-only cutoffs in the genuine time-jet chart. The spectral
symbol is compact and globally smooth, while its exact operator equals
the original amplitude's operator multiplied by an output cutoff. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace PlanarNikodym

theorem exists_glyz_output_cutoff_parabolic_symbols {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (hi : ∀ x ∈ e.target, ContDiffAt ℝ ∞ e.symm x) (σ : Fin (n + 1) ↪ Fin (d + 2))
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : Parameters 2 d × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set ((ℝ × Aux (d + 2)) × Aux (n + 1))} (hK : IsCompact K) (hKT : K ⊆ e.target)
    {J : Set ℝ} (hJ : IsCompact J) :
    ∃ (ρ : ((ℝ × Aux (d + 2)) × Aux (n + 1)) → ℝ)
      (A : GlyzParabolicSymbolVariables d n → ℂ) (H : GlyzParabolicSymbolVariables d n → ℝ),
      ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ (∀ z, 0 ≤ ρ z ∧ ρ z ≤ 1) ∧
      (∀ z ∈ K, ρ z = 1) ∧ tsupport ρ ⊆ e.target ∧
      ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧ tsupport A ⊆ {z | z.1.1 ∈ e.target} ∧
      ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ {z | z.1.1 ∈ e.target} ∧
      ∀ q y τ, ∀ η ∈ J, ∀ δ ∈ Icc (0 : ℝ) 1, ∀ α : ℝ,
        A (((q, y), (τ, η)), δ) * Complex.exp
          (((α * H (((q, y), (τ, η)), δ) : ℝ) : ℂ) * Complex.I) =
          (ρ (q, y) : ℂ) * inverseChartTaylorAmplitude e σ a Φ
            ((((q, y), (τ, η)), α, δ)) := by
  obtain ⟨ρ, N, hρ, hcρ, hrange, _, hKN, hN1, hρT⟩ :=
    exists_compact_smooth_cutoff hK e.open_target hKT
  obtain ⟨χτ, Nτ, hτ, hcτ, _, _, hτN, hτ1, _⟩ :=
    exists_compact_smooth_cutoff (K := Icc (-1 : ℝ) 1) (S := univ)
      isCompact_Icc isOpen_univ (subset_univ _)
  obtain ⟨χη, Nη, hη, hcη, _, _, hηN, hη1, _⟩ :=
    exists_compact_smooth_cutoff (S := univ) hJ isOpen_univ (subset_univ _)
  obtain ⟨χδ, Nδ, hδ, hcδ, _, _, hδN, hδ1, _⟩ :=
    exists_compact_smooth_cutoff (K := Icc (0 : ℝ) 1) (S := univ)
      isCompact_Icc isOpen_univ (subset_univ _)
  let χ : GlyzParabolicSymbolVariables d n → ℝ :=
    fun z => ρ z.1.1 * (χτ z.1.2.1 * χη z.1.2.2) * χδ z.2
  let L : Set (GlyzParabolicSymbolVariables d n) :=
    (tsupport ρ ×ˢ (tsupport χτ ×ˢ tsupport χη)) ×ˢ tsupport χδ
  have hL : IsCompact L := (hcρ.isCompact.prod (hcτ.isCompact.prod hcη.isCompact)).prod hcδ.isCompact
  have hsupp : Function.support χ ⊆ L := by
    intro z hz
    obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hz
    obtain ⟨h₃, h₄⟩ := mul_ne_zero_iff.mp h₁
    obtain ⟨h₅, h₆⟩ := mul_ne_zero_iff.mp h₄
    exact ⟨⟨subset_tsupport _ h₃, subset_tsupport _ h₅, subset_tsupport _ h₆⟩,
      subset_tsupport _ h₂⟩
  have htχ : tsupport χ ⊆ L := closure_minimal hsupp hL.isClosed
  have hcχ : HasCompactSupport χ := hL.of_isClosed_subset isClosed_closure htχ
  have hχ : ContDiff ℝ ∞ χ :=
    ((hρ.comp contDiff_fst.fst).mul
      ((hτ.comp contDiff_fst.snd.fst).mul (hη.comp contDiff_fst.snd.snd))).mul
        (hδ.comp contDiff_snd)
  let U : Set (GlyzParabolicSymbolVariables d n) := {z | z.1.1 ∈ e.target}
  have hU : IsOpen U := e.open_target.preimage (by fun_prop)
  have hχU : tsupport χ ⊆ U := fun _ hz => hρT (htχ hz).1.1
  obtain ⟨A, H, hA, hcA, hAU, hH, hcH, hHU, hAe, heq⟩ :=
    exists_glyz_compact_phase_amplitude_of_cutoff (glyzInverseChartBaseSymbol e σ a)
      (glyzInverseChartRemainderProfile e σ Φ) χ hχ hcχ hU hχU
      (fun z hz => contDiffAt_glyzInverseChartBaseSymbol e σ ha z (hi _ hz))
      (fun z hz => contDiffAt_glyzInverseChartRemainderProfile e σ hΦ z (hi _ hz))
  refine ⟨ρ, A, H, hρ, hcρ, hrange, fun z hz => hN1 z (hKN hz), hρT,
    hA, hcA, hAU, hH, hcH, hHU, ?_⟩
  intro q y τ η hηJ δ hδI α
  rw [heq, inverseChartTaylorAmplitude_eq_base_mul_profile]
  by_cases hτI : τ ∈ Icc (-1 : ℝ) 1
  · have hχeq : χ (((q, y), (τ, η)), δ) = ρ (q, y) := by
      simp only [χ, hτ1 τ (hτN hτI), hη1 η (hηN hηJ), hδ1 δ (hδN hδI), mul_one]
    rw [hχeq]
  · have hw : timePartitionWindow τ = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hτI (tsupport_timePartitionWindow_subset ht))
    simp only [glyzInverseChartBaseSymbol, hw, Complex.ofReal_zero, mul_zero, zero_mul]

/-- A global identity with the same original amplitude. The cutoff is
outside the extension integral and vanishes beyond the chart target. -/
theorem Family.compact_parabolic_eq_output_cutoff_timeSlice {d n : ℕ} (G : Family 2 d)
    (hm : n + 1 ≤ d + 2) (σ : Fin (n + 1) ↪ Fin (d + 2))
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (he : ∀ x, e x = (x.1, G.movingLowerJetMap hm σ x))
    (a : Parameters 2 d × ℝ × ℝ → ℂ)
    (hΦ : ContDiff ℝ ∞ (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1))
    (ρ : ((ℝ × Aux (d + 2)) × Aux (n + 1)) → ℝ) (hρT : tsupport ρ ⊆ e.target)
    (A : GlyzParabolicSymbolVariables d n → ℂ) (H : GlyzParabolicSymbolVariables d n → ℝ)
    {J : Set ℝ}
    (hsymbol : ∀ q y τ, ∀ η ∈ J, ∀ δ ∈ Icc (0 : ℝ) 1, ∀ α : ℝ,
      A (((q, y), (τ, η)), δ) * Complex.exp
        (((α * H (((q, y), (τ, η)), δ) : ℝ) : ℂ) * Complex.I) =
        (ρ (q, y) : ℂ) * inverseChartTaylorAmplitude e σ a
          (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) ((((q, y), (τ, η)), α, δ)))
    (h : ℝ × ℝ → ℂ) (hhJ : ∀ t η, η ∉ J → h (t, η) = 0)
    (q : ℝ × Aux (d + 2)) (r : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (w : Aux (n + 1)) :
    δ • polynomialExtension
      (glyzCompactParabolicAmplitude A H q δ hδ.ne' (r * δ ^ (n + 1)))
      (fun x => h (q.1 + δ * x.1, x.2)) (r * δ ^ n) w =
      (ρ (q, (lowerDegreeDilation n δ hδ.ne').symm w) : ℂ) *
        timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h r q.1 δ
          (parameterFrame d (q.2 + coordinateInsertion σ
            (e.symm (q, (lowerDegreeDilation n δ hδ.ne').symm w)).2)) := by
  let y := (lowerDegreeDilation n δ hδ.ne').symm w
  let p := parameterFrame d (q.2 + coordinateInsertion σ (e.symm (q, y)).2)
  let b : Aux (n + 1) → ℝ → ℝ → ℂ := fun _ τ η =>
    actualTaylorAmplitude a (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) n r q.1 δ p τ η
  have hAeq (τ : ℝ) {η : ℝ} (hη : η ∈ J) :
      glyzCompactParabolicAmplitude A H q δ hδ.ne' (r * δ ^ (n + 1)) w τ η =
        (ρ (q, y) : ℂ) * b w τ η := by
    unfold glyzCompactParabolicAmplitude
    rw [hsymbol q _ τ η hη δ ⟨hδ.le, hδ1⟩]
    congr 1
    unfold inverseChartTaylorAmplitude
    exact rescaledTaylorAmplitude_eq_actualTaylorAmplitude a hΦ n _ r q.1 δ τ η
  have hpoly : polynomialExtension
      (glyzCompactParabolicAmplitude A H q δ hδ.ne' (r * δ ^ (n + 1)))
      (fun x => h (q.1 + δ * x.1, x.2)) (r * δ ^ n) w =
      (ρ (q, y) : ℂ) * polynomialExtension b
        (fun x => h (q.1 + δ * x.1, x.2)) (r * δ ^ n) w := by
    unfold polynomialExtension
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with η
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with τ
    by_cases hη : η ∈ J
    · rw [hAeq τ hη]
      ring
    · simp only [hhJ _ η hη, mul_zero]
  change _ = (ρ (q, y) : ℂ) * timeSliceExtension
    (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h r q.1 δ p
  rw [hpoly]
  by_cases hρ : ρ (q, y) = 0
  · simp only [hρ, Complex.ofReal_zero, zero_mul, smul_zero]
  · have htarget : (q, y) ∈ e.target := hρT (subset_tsupport _ hρ)
    have htime : timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h r q.1 δ p =
        δ • polynomialExtension b (fun x => h (q.1 + δ * x.1, x.2)) (r * δ ^ n) w := by
      rw [timeSliceExtension_eq_taylor _ a h n r q.1 hδ]
      congr 1
      unfold polynomialExtension
      apply integral_congr_ae
      filter_upwards [] with η
      apply integral_congr_ae
      filter_upwards [] with τ
      have hp := G.timeTaylorEval_in_scaled_smooth_chart hm σ e he hΦ q δ hδ.ne' w htarget τ
      have hphase : r * η * timeTaylorEval (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
          n p q.1 (q.1 + δ * τ) = (r * δ ^ n) * η * jetPolynomial w τ := by
        rw [hp]
        ring
      unfold phaseOscillation
      rw [hphase]
    rw [htime]
    exact (mul_smul_comm _ _ _).symm

/-- Construct the compact symbols before every scale, frequency, input,
and output. No symbol identity or decoupling certificate is an input. -/
theorem Family.exists_compact_parabolic_representation {d n : ℕ} (G : Family 2 d)
    (hm : n + 1 ≤ d + 2) (σ : Fin (n + 1) ↪ Fin (d + 2))
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (he : ∀ x, e x = (x.1, G.movingLowerJetMap hm σ x))
    (hi : ∀ x ∈ e.target, ContDiffAt ℝ ∞ e.symm x)
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    (hΦ : ContDiff ℝ ∞ (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1))
    {K : Set ((ℝ × Aux (d + 2)) × Aux (n + 1))} (hK : IsCompact K) (hKT : K ⊆ e.target)
    {J : Set ℝ} (hJ : IsCompact J) :
    ∃ (ρ : ((ℝ × Aux (d + 2)) × Aux (n + 1)) → ℝ)
      (A : GlyzParabolicSymbolVariables d n → ℂ) (H : GlyzParabolicSymbolVariables d n → ℝ),
      ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ (∀ z, 0 ≤ ρ z ∧ ρ z ≤ 1) ∧
      (∀ z ∈ K, ρ z = 1) ∧ tsupport ρ ⊆ e.target ∧
      ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧ tsupport A ⊆ {z | z.1.1 ∈ e.target} ∧
      ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ {z | z.1.1 ∈ e.target} ∧
      ∀ (h : ℝ × ℝ → ℂ), (∀ t η, η ∉ J → h (t, η) = 0) →
        ∀ (q : ℝ × Aux (d + 2)) (r δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → ∀ w : Aux (n + 1),
          δ • polynomialExtension
            (glyzCompactParabolicAmplitude A H q δ hδ.ne' (r * δ ^ (n + 1)))
            (fun x => h (q.1 + δ * x.1, x.2)) (r * δ ^ n) w =
            (ρ (q, (lowerDegreeDilation n δ hδ.ne').symm w) : ℂ) *
              timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h r q.1 δ
                (parameterFrame d (q.2 + coordinateInsertion σ
                  (e.symm (q, (lowerDegreeDilation n δ hδ.ne').symm w)).2)) := by
  obtain ⟨ρ, A, H, hρ, hcρ, hrange, hρ1, hρT, hA, hcA, hAT, hH, hcH, hHT, hsymbol⟩ :=
    exists_glyz_output_cutoff_parabolic_symbols e hi σ ha hΦ hK hKT hJ
  refine ⟨ρ, A, H, hρ, hcρ, hrange, hρ1, hρT, hA, hcA, hAT, hH, hcH, hHT, ?_⟩
  intro h hhJ q r δ hδ hδ1 w
  exact G.compact_parabolic_eq_output_cutoff_timeSlice hm σ e he a hΦ ρ hρT A H
    hsymbol h hhJ q r hδ hδ1 w

end PlanarNikodym
