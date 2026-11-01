import PlanarNikodym.Analysis.Fourier.GlyzParabolicOutputCutoff

/-! Exact parabolic coordinates for a sharp parent interval. No smooth
time window is inserted into the original amplitude. The normalized
input itself supplies the time support on [0,1]. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace PlanarNikodym

def glyzRawExtension {P : Type} (Φ : P × ℝ → ℝ) (a : P × ℝ × ℝ → ℂ)
    (h : Plane → ℂ) (r : ℝ) (p : P) : ℂ :=
  ∫ η : ℝ, ∫ t : ℝ, phaseOscillation (fun s => Φ (p, s)) (r * η) t *
    a (p, t, η) * h (t, η)

def glyzRawTaylorAmplitude {P : Type} (a : P × ℝ × ℝ → ℂ) (Φ : P × ℝ → ℝ)
    (n : ℕ) (r c δ : ℝ) (p : P) (τ η : ℝ) : ℂ :=
  a (p, c + δ * τ, η) * frequencyTaylorCorrection Φ n r δ ((p, c, τ), η)

theorem glyzRawExtension_eq_taylor {P : Type} (Φ : P × ℝ → ℝ)
    (a : P × ℝ × ℝ → ℂ) (h : Plane → ℂ) (n : ℕ)
    (r c : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : P) :
    glyzRawExtension Φ a h r p = δ • ∫ η : ℝ, ∫ τ : ℝ,
      phaseOscillation (timeTaylorEval Φ n p c) (r * η) (c + δ * τ) *
        glyzRawTaylorAmplitude a Φ n r c δ p τ η * h (c + δ * τ, η) := by
  unfold glyzRawExtension
  conv_lhs => arg 2; ext η; rw [integral_time_affine _ c hδ]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with η
  apply congrArg (fun z : ℂ => δ • z)
  apply integral_congr_ae
  filter_upwards [] with τ
  rw [phaseOscillation_eq_taylor_mul_actualCorrection Φ n]
  simp only [glyzRawTaylorAmplitude]
  ring

def glyzRawInverseChartBaseSymbol {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (σ : Fin (n + 1) ↪ Fin (d + 2)) (a : Parameters 2 d × ℝ × ℝ → ℂ)
    (z : GlyzParabolicSymbolVariables d n) : ℂ :=
  a (parameterFrame d (z.1.1.1.2 + coordinateInsertion σ (e.symm z.1.1).2),
    z.1.1.1.1 + z.2 * z.1.2.1, z.1.2.2)

theorem contDiffAt_glyzRawInverseChartBaseSymbol {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (σ : Fin (n + 1) ↪ Fin (d + 2))
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    (z : GlyzParabolicSymbolVariables d n) (hi : ContDiffAt ℝ ∞ e.symm z.1.1) :
    ContDiffAt ℝ ∞ (glyzRawInverseChartBaseSymbol e σ a) z := by
  have hei : ContDiffAt ℝ ∞ (fun y : GlyzParabolicSymbolVariables d n => e.symm y.1.1) z :=
    hi.comp z contDiffAt_fst.fst
  have hp : ContDiffAt ℝ ∞ (fun y : GlyzParabolicSymbolVariables d n =>
      parameterFrame d (y.1.1.1.2 + coordinateInsertion σ (e.symm y.1.1).2)) z :=
    (parameterFrame d).contDiff.contDiffAt.comp z
      (contDiffAt_fst.fst.fst.snd.add ((coordinateInsertion σ).contDiff.contDiffAt.comp z hei.snd))
  exact ha.contDiffAt.comp z
    (hp.prodMk ((contDiffAt_fst.fst.fst.fst.add (contDiffAt_snd.mul contDiffAt_fst.snd.fst)).prodMk
      contDiffAt_fst.snd.snd))

theorem glyzRawInverseChartSymbol_eq_actual {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (σ : Fin (n + 1) ↪ Fin (d + 2)) (a : Parameters 2 d × ℝ × ℝ → ℂ)
    {Φ : Parameters 2 d × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (q : ℝ × Aux (d + 2)) (y : Aux (n + 1)) (r δ τ η : ℝ) :
    glyzRawInverseChartBaseSymbol e σ a (((q, y), (τ, η)), δ) * Complex.exp
      ((((r * δ ^ (n + 1)) *
        glyzInverseChartRemainderProfile e σ Φ (((q, y), (τ, η)), δ) : ℝ) : ℂ) * Complex.I) =
      glyzRawTaylorAmplitude a Φ n r q.1 δ
        (parameterFrame d (q.2 + coordinateInsertion σ (e.symm (q, y)).2)) τ η := by
  unfold glyzRawInverseChartBaseSymbol glyzRawTaylorAmplitude frequencyTaylorCorrection
  rw [timeTaylor_remainder_eq_integral hΦ]
  unfold glyzInverseChartRemainderProfile
  congr 2
  push_cast
  ring

theorem exists_glyz_raw_output_cutoff_parabolic_symbols {d n : ℕ}
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
      ∀ q y, ∀ τ ∈ Icc (0 : ℝ) 1, ∀ η ∈ J, ∀ δ ∈ Icc (0 : ℝ) 1, ∀ α : ℝ,
        A (((q, y), (τ, η)), δ) * Complex.exp
          (((α * H (((q, y), (τ, η)), δ) : ℝ) : ℂ) * Complex.I) =
          (ρ (q, y) : ℂ) * (glyzRawInverseChartBaseSymbol e σ a (((q, y), (τ, η)), δ) *
            Complex.exp (((α * glyzInverseChartRemainderProfile e σ Φ
              (((q, y), (τ, η)), δ) : ℝ) : ℂ) * Complex.I)) := by
  obtain ⟨ρ, N, hρ, hcρ, hrange, _, hKN, hN1, hρT⟩ :=
    exists_compact_smooth_cutoff hK e.open_target hKT
  obtain ⟨χτ, Nτ, hτ, hcτ, _, _, hτN, hτ1, _⟩ :=
    exists_compact_smooth_cutoff (K := Icc (0 : ℝ) 1) (S := univ)
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
    exists_glyz_compact_phase_amplitude_of_cutoff (glyzRawInverseChartBaseSymbol e σ a)
      (glyzInverseChartRemainderProfile e σ Φ) χ hχ hcχ hU hχU
      (fun z hz => contDiffAt_glyzRawInverseChartBaseSymbol e σ ha z (hi _ hz))
      (fun z hz => contDiffAt_glyzInverseChartRemainderProfile e σ hΦ z (hi _ hz))
  refine ⟨ρ, A, H, hρ, hcρ, hrange, fun z hz => hN1 z (hKN hz), hρT,
    hA, hcA, hAU, hH, hcH, hHU, ?_⟩
  intro q y τ hτI η hηJ δ hδI α
  rw [heq]
  have hχeq : χ (((q, y), (τ, η)), δ) = ρ (q, y) := by
    simp only [χ, hτ1 τ (hτN hτI), hη1 η (hηN hηJ), hδ1 δ (hδN hδI), mul_one]
  rw [hχeq]

theorem Family.compact_parabolic_eq_output_cutoff_rawExtension {d n : ℕ} (G : Family 2 d)
    (hm : n + 1 ≤ d + 2) (σ : Fin (n + 1) ↪ Fin (d + 2))
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (he : ∀ x, e x = (x.1, G.movingLowerJetMap hm σ x))
    (a : Parameters 2 d × ℝ × ℝ → ℂ)
    (hΦ : ContDiff ℝ ∞ (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1))
    (ρ : ((ℝ × Aux (d + 2)) × Aux (n + 1)) → ℝ) (hρT : tsupport ρ ⊆ e.target)
    (A : GlyzParabolicSymbolVariables d n → ℂ) (H : GlyzParabolicSymbolVariables d n → ℝ)
    {J : Set ℝ}
    (hsymbol : ∀ q y, ∀ τ ∈ Icc (0 : ℝ) 1, ∀ η ∈ J, ∀ δ ∈ Icc (0 : ℝ) 1, ∀ α : ℝ,
      A (((q, y), (τ, η)), δ) * Complex.exp
        (((α * H (((q, y), (τ, η)), δ) : ℝ) : ℂ) * Complex.I) =
        (ρ (q, y) : ℂ) * (glyzRawInverseChartBaseSymbol e σ a (((q, y), (τ, η)), δ) *
          Complex.exp (((α * glyzInverseChartRemainderProfile e σ
            (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
            (((q, y), (τ, η)), δ) : ℝ) : ℂ) * Complex.I)))
    (h : ℝ × ℝ → ℂ)
    (q : ℝ × Aux (d + 2)) (r : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hh : Function.support h ⊆ Icc q.1 (q.1 + δ) ×ˢ J)
    (w : Aux (n + 1)) :
    δ • polynomialExtension
      (glyzCompactParabolicAmplitude A H q δ hδ.ne' (r * δ ^ (n + 1)))
      (fun x => h (q.1 + δ * x.1, x.2)) (r * δ ^ n) w =
      (ρ (q, (lowerDegreeDilation n δ hδ.ne').symm w) : ℂ) *
        glyzRawExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h r
          (parameterFrame d (q.2 + coordinateInsertion σ
            (e.symm (q, (lowerDegreeDilation n δ hδ.ne').symm w)).2)) := by
  let y := (lowerDegreeDilation n δ hδ.ne').symm w
  let p := parameterFrame d (q.2 + coordinateInsertion σ (e.symm (q, y)).2)
  let b : Aux (n + 1) → ℝ → ℝ → ℂ := fun _ τ η =>
    glyzRawTaylorAmplitude a (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) n r q.1 δ p τ η
  have hzero (τ η : ℝ) (hz : ¬ (τ ∈ Icc (0 : ℝ) 1 ∧ η ∈ J)) :
      h (q.1 + δ * τ, η) = 0 := by
    by_contra hn
    have hs := hh hn
    apply hz
    exact ⟨⟨by nlinarith [hs.1.1], by nlinarith [hs.1.2]⟩, hs.2⟩
  have hAeq (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) {η : ℝ} (hη : η ∈ J) :
      glyzCompactParabolicAmplitude A H q δ hδ.ne' (r * δ ^ (n + 1)) w τ η =
        (ρ (q, y) : ℂ) * b w τ η := by
    unfold glyzCompactParabolicAmplitude
    rw [hsymbol q _ τ hτ η hη δ ⟨hδ.le, hδ1⟩]
    congr 1
    exact glyzRawInverseChartSymbol_eq_actual e σ a hΦ q y r δ τ η
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
    by_cases hy : τ ∈ Icc (0 : ℝ) 1 ∧ η ∈ J
    · rw [hAeq τ hy.1 hy.2]
      ring
    · simp only [hzero τ η hy, mul_zero]
  change _ = (ρ (q, y) : ℂ) * glyzRawExtension
    (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h r p
  rw [hpoly]
  by_cases hρ : ρ (q, y) = 0
  · simp only [hρ, Complex.ofReal_zero, zero_mul, smul_zero]
  · have htarget : (q, y) ∈ e.target := hρT (subset_tsupport _ hρ)
    have htime : glyzRawExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h r p =
        δ • polynomialExtension b (fun x => h (q.1 + δ * x.1, x.2)) (r * δ ^ n) w := by
      rw [glyzRawExtension_eq_taylor _ a h n r q.1 hδ]
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

theorem Family.exists_compact_raw_parabolic_representation {d n : ℕ} (G : Family 2 d)
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
      ∀ (h : ℝ × ℝ → ℂ) (q : ℝ × Aux (d + 2)) (r δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
        Function.support h ⊆ Icc q.1 (q.1 + δ) ×ˢ J → ∀ w : Aux (n + 1),
          δ • polynomialExtension
            (glyzCompactParabolicAmplitude A H q δ hδ.ne' (r * δ ^ (n + 1)))
            (fun x => h (q.1 + δ * x.1, x.2)) (r * δ ^ n) w =
            (ρ (q, (lowerDegreeDilation n δ hδ.ne').symm w) : ℂ) *
              glyzRawExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h r
                (parameterFrame d (q.2 + coordinateInsertion σ
                  (e.symm (q, (lowerDegreeDilation n δ hδ.ne').symm w)).2)) := by
  obtain ⟨ρ, A, H, hρ, hcρ, hrange, hρ1, hρT, hA, hcA, hAT, hH, hcH, hHT, hsymbol⟩ :=
    exists_glyz_raw_output_cutoff_parabolic_symbols e hi σ ha hΦ hK hKT hJ
  refine ⟨ρ, A, H, hρ, hcρ, hrange, hρ1, hρT, hA, hcA, hAT, hH, hcH, hHT, ?_⟩
  intro h q r δ hδ hδ1 hh w
  exact G.compact_parabolic_eq_output_cutoff_rawExtension hm σ e he a hΦ ρ hρT A H
    hsymbol h q r hδ hδ1 hh w

end PlanarNikodym
