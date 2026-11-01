import PlanarNikodym.Analysis.Fourier.GlyzLowerOriginalParentStep
import PlanarNikodym.Analysis.Fourier.GlyzFiniteParabolicBudget
import PlanarNikodym.Analysis.Fourier.GlyzRelativeEpsilonIteration
import PlanarNikodym.Analysis.Fourier.GlyzVariableTargetIteration
import PlanarNikodym.Analysis.Fourier.GlyzCascadeExponents

/-! Genuine lower-degree decoupling relative to any existing dyadic
scale. All norms use the original amplitude and full parameter volume. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace PlanarNikodym

set_option maxHeartbeats 1200000 in
theorem Family.exists_glyz_lower_relative_power {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ K)
    (k : ℕ) (hk : 0 < k) (hkdim : k + 1 ≤ d + 2) (s : ℕ)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent k ≤ p)
    {ε rmin rmax Q : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ N A : ℕ, A ≤ glyzVariableFinalDepth k N - s →
      ∀ r : ℝ, (2 : ℝ) ^ N ≤ r → r ≤ (2 : ℝ) ^ (N + 1) →
      ∀ g : Plane → ℂ, Integrable g →
      Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1} →
      Function.support g ⊆ {y | y.2 ∈ Icc rmin rmax} →
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      let F := glyzVariableFinalDepth k N - s
      (∑ i ∈ Finset.range (2 ^ A),
        ∫⁻ x, ‖glyzRawExtension Φ a (glyzDyadicInput A i g) r x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent k / 2 - 1) * ((F - A : ℕ) : ℝ) + ε * N)) *
          (∑ i ∈ Finset.range (2 ^ F),
            ∫⁻ x, ‖glyzRawExtension Φ a (glyzDyadicInput F i g) r x‖ₑ ^ (p : ℝ)) +
        ENNReal.ofReal (C * (2 : ℝ) ^ (-Q * N)) * (∫⁻ y, ‖g y‖ₑ) ^ (p : ℝ) := by
  classical
  let σ : ℝ := (p : ℝ) - glyzCriticalExponent k / 2 - 1
  have hp1 : (1 : ℝ) ≤ p :=
    (one_le_glyzCriticalNNExponent hk).trans hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  have hcrit : glyzCriticalExponent k ≤ (p : ℝ) := hp
  have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hσ : 0 ≤ σ := by
    have h2 : 2 ≤ glyzCriticalExponent k := by
      dsimp [glyzCriticalExponent]
      nlinarith
    dsimp [σ]
    linarith
  obtain ⟨ζ, η, hζ, hη, hiter⟩ :=
    exists_glyz_actual_kernel_relative_epsilon_iteration (X := Parameters 2 d) k hk hp1 hσ hε
  let W := Module.finrank ℝ (GlyzConeSpace k) + 1
  have hW : Module.finrank ℝ (GlyzConeSpace k) < W := by dsimp [W]; omega
  let Q' := Q + (σ + ε)
  obtain ⟨M, hfinite⟩ := exists_glyz_finite_parabolic_budget k W hW p hp0 η
    (show 0 ≤ (p : ℝ) - glyzCriticalExponent k / 2 - 1 + η from add_nonneg hσ hη.le)
    hζ Q'
  obtain ⟨τ, hτ, m, C, D, L, Cg, b, Cj, V, cJ, hconst, hparent⟩ :=
    G.exists_glyz_lower_original_parent_step hG ha hc hK hdet has k hk hkdim W M hW hp hη hrmin
      (rmax := rmax)
  let card : ℝ≥0∞ := (m : ℝ≥0∞) ^ ((p : ℝ) - 1)
  let u := fun i => card * (ENNReal.ofReal (b i))⁻¹ * ENNReal.ofReal (Cj i)
  let v := fun i => card * ENNReal.ofReal (V i) * (ENNReal.ofReal (b i))⁻¹ * (cJ i : ℝ≥0∞)⁻¹
  have hcard : card ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hp1) (by simp)
  have hb (i : Fin m) : ENNReal.ofReal (b i) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (hconst i).2.2.2.2.1).ne'
  have hcJ (i : Fin m) : (cJ i : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (hconst i).2.2.2.2.2.2.1.ne'
  have hu (i : Fin m) : u i ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hcard (ENNReal.inv_ne_top.mpr (hb i)))
      ENNReal.ofReal_ne_top
  have hv (i : Fin m) : v i ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hcard ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_top.mpr (hb i))) (ENNReal.inv_ne_top.mpr (hcJ i))
  obtain ⟨C₀, E₀, hC₀, hE₀, hcoeff⟩ := hfinite m u v C D L Cg hu hv
    (fun i => (hconst i).1.le) (fun i => (hconst i).2.1) (fun i => (hconst i).2.2.1.le)
  obtain ⟨cτ, hcτ⟩ :=
    exists_pow_lt_of_lt_one hτ (by norm_num : (1 / 2 : ℝ) < 1)
  have hτscale : glyzDyadicScale cτ ≤ τ := by
    exact (show glyzDyadicScale cτ < τ by
      simpa only [glyzDyadicScale, one_div, inv_pow] using hcτ).le
  obtain ⟨cr, hcr⟩ := exists_glyz_variable_spectral_offset rmin
  let c := max (max cτ cr) (k * (s + 1))
  have hcτc : cτ ≤ c := (le_max_left cτ cr).trans (le_max_left _ _)
  have hcrc : cr ≤ c := (le_max_right cτ cr).trans (le_max_left _ _)
  have hcs : k * (s + 1) ≤ c := le_max_right _ _
  have hrad : 40 * Real.pi / rmin ≤ (2 : ℝ) ^ c :=
    hcr.trans (pow_le_pow_right₀ (by norm_num) hcrc)
  obtain ⟨A₀, hA₀, hresult⟩ := hiter c C₀ E₀ Q hC₀ hE₀ hQ
  refine ⟨A₀, hA₀, fun N A hAF r hr hr' g hg hgt hgr => ?_⟩
  let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
  let H := glyzRawKernel Φ a r
  have hΦ : ContDiff ℝ ∞ Φ := hG.comp (contDiff_snd.prodMk contDiff_fst)
  have hH : ContDiff ℝ ∞ H := contDiff_glyzRawKernel hΦ ha r
  have hcH : HasCompactSupport H := hasCompactSupport_glyzRawKernel Φ hc r
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hα (n : ℕ) : |r * glyzDyadicScale n ^ (k + 1)| ≤ (2 : ℝ) ^ (N + 1) :=
    (glyz_variable_alpha_le_frequency k n hr0.le).trans hr'
  have hstep : ∀ n n' : ℕ, n < n' →
      k * (n' - n) + (⌈ζ * N⌉₊ + c) ≤ n →
      k * n' + (⌈ζ * N⌉₊ + c) ≤ N → ∀ i < 2 ^ n,
      (∫⁻ x, ‖glyzDyadicKernelPiece H g n i x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C₀ * (2 : ℝ) ^ ((σ + η) * ((n' - n : ℕ) : ℝ))) *
          glyzDyadicBlock
            (fun j => ∫⁻ x, ‖glyzDyadicKernelPiece H g n' j x‖ₑ ^ (p : ℝ)) n' n i +
        ENNReal.ofReal (E₀ * (2 : ℝ) ^ (-Q' * N)) *
          (∫⁻ y, ‖glyzDyadicInput n i g y‖ₑ) ^ (p : ℝ) := by
    intro n n' hnn' hparentbudget hfreq i _hi
    have hn' : n' ≤ N := by
      have := Nat.le_mul_of_pos_left n' hk
      omega
    have hnN : n ≤ N := hnn'.le.trans hn'
    have hqN : n' - n ≤ N := (Nat.sub_le _ _).trans hn'
    have hcn : c ≤ n := by omega
    have hsmall : glyzDyadicScale n ≤ τ :=
      (glyzDyadicScale_antitone (hcτc.trans hcn)).trans hτscale
    have hz : ζ * N + c ≤ (⌈ζ * N⌉₊ + c : ℕ) := by
      push_cast
      exact add_le_add_left (Nat.le_ceil (ζ * (N : ℝ))) (c : ℝ)
    have hscale := glyz_variable_spectral_budget_of_frequency k N n (n' - n) c
      (⌈ζ * N⌉₊ + c) hr hζ.le hrmin hz hrad hparentbudget
      (by simpa only [Nat.add_sub_of_le hnn'.le] using hfreq)
    have hscale' :
        1 + 2 * ((1 + |r * glyzDyadicScale n ^ (k + 1)|) * ((2 : ℝ) ^ (ζ * N))) ≤
          (rmin / 4) * ((r * glyzDyadicScale n ^ k) / (2 * Real.pi)) *
            glyzDyadicScale (n' - n) ^ k := by
      simpa only [pow_succ, mul_assoc] using hscale
    have hpar := hparent n (n' - n) i r ((2 : ℝ) ^ (ζ * N))
      hsmall hr0 (by positivity) hscale' g hg hgr
    have hcf := hcoeff N n (n' - n) hnN hqN (r * glyzDyadicScale n ^ (k + 1)) (hα n)
    have hsumu :
        (∑ l, u l * glyzParabolicPowerCoefficient k p η (C l) (Cg l) (n' - n)) =
        card * (∑ l, (ENNReal.ofReal (b l))⁻¹ *
          glyzParabolicPowerCoefficient k p η (C l) (Cg l) (n' - n) *
          ENNReal.ofReal (Cj l)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      dsimp only [u]
      ring
    have hsumv :
        (∑ l, v l * glyzParabolicErrorCoefficient k W M p η (C l) (D l) (L l)
          (glyzDyadicScale n) (r * glyzDyadicScale n ^ (k + 1)) (n' - n)
          ((2 : ℝ) ^ (ζ * N))) =
        card * (∑ l, ENNReal.ofReal (V l) * (ENNReal.ofReal (b l))⁻¹ * (cJ l : ℝ≥0∞)⁻¹ *
          glyzParabolicErrorCoefficient k W M p η (C l) (D l) (L l)
            (glyzDyadicScale n) (r * glyzDyadicScale n ^ (k + 1)) (n' - n)
            ((2 : ℝ) ^ (ζ * N))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      dsimp only [v]
      ring
    let energy := ∑ j ∈ Finset.range (2 ^ (n' - n)),
      ∫⁻ x, ‖glyzRawExtension Φ a
        (glyzDyadicInput n' (i * 2 ^ (n' - n) + j) g) r x‖ₑ ^ (p : ℝ)
    have hpar' : (∫⁻ x, ‖glyzRawExtension Φ a (glyzDyadicInput n i g) r x‖ₑ ^ (p : ℝ)) ≤
        (∑ l, u l * glyzParabolicPowerCoefficient k p η (C l) (Cg l) (n' - n)) * energy +
        (∑ l, v l * glyzParabolicErrorCoefficient k W M p η (C l) (D l) (L l)
          (glyzDyadicScale n) (r * glyzDyadicScale n ^ (k + 1)) (n' - n)
          ((2 : ℝ) ^ (ζ * N))) * (∫⁻ y, ‖glyzDyadicInput n i g y‖ₑ) ^ (p : ℝ) := by
      rw [hsumu, hsumv]
      simpa only [card, energy, Φ, Nat.add_sub_of_le hnn'.le, mul_add, mul_assoc] using hpar
    have hbnd := hpar'.trans (add_le_add
      (mul_le_mul_left hcf.1 energy)
      (mul_le_mul_left hcf.2 ((∫⁻ y, ‖glyzDyadicInput n i g y‖ₑ) ^ (p : ℝ))))
    simpa only [glyzRawExtension_dyadicInput_eq_piece hΦ ha hc hg r,
      glyzDyadicBlock, energy, Φ, H, σ] using hbnd
  have hTF : glyzVariableTerminalDepth k N (⌈ζ * N⌉₊ + c) ≤
      glyzVariableFinalDepth k N - s :=
    glyz_variable_terminal_le_coarse k N (⌈ζ * N⌉₊ + c) s hk (by nlinarith)
  have hFN : glyzVariableFinalDepth k N - s ≤ N :=
    (Nat.sub_le _ _).trans (glyzVariableFinalDepth_le k N hk)
  have h := hresult N A (glyzVariableFinalDepth k N - s) hAF hFN hTF (Nat.sub_le _ _)
    volume H g hH hcH hg hgt hstep
  simpa only [glyzRawExtension_eq_compactKernel hΦ ha hc hg r,
    glyzRawExtension_dyadicInput_eq_piece hΦ ha hc hg r,
    glyzDyadicKernelEnergy, H, Φ, σ] using h


end PlanarNikodym
