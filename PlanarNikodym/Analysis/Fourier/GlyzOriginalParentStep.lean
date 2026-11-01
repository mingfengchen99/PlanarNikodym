import PlanarNikodym.Analysis.Fourier.GlyzOriginalPatchTransport
import PlanarNikodym.Analysis.Fourier.GlyzParabolicErrorReduction

/-! Actual full-parameter parent refinement from the cinematic
nondegeneracy of the original smooth phase. A finite atlas is constructed
before all scales and input functions. The error uses only the original
parent L¹ mass; all displayed coefficients are fixed finite sums. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace PlanarNikodym

theorem Family.exists_glyz_original_parent_step {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ p t η, a (p, t, η) ≠ 0 → (t, p) ∈ K)
    (W M : ℕ) (hW : Module.finrank ℝ (GlyzConeSpace (d + 1)) < W)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε rmin rmax : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ m : ℕ,
      ∃ C D L Cg b Cj : Fin m → ℝ, ∃ c : Fin m → ℝ≥0,
      (∀ l, 0 < C l ∧ 0 ≤ D l ∧ 0 < L l ∧ 0 < Cg l ∧
        0 < b l ∧ 0 < Cj l ∧ 0 < c l) ∧
      ∀ (n q i : ℕ) (r T : ℝ), glyzDyadicScale n ≤ τ → 0 < r → 0 < T →
      1 + 2 * ((1 + |r * glyzDyadicScale n ^ (d + 2)|) * T) ≤
        (rmin / 4) * ((r * glyzDyadicScale n ^ (d + 1)) / (2 * Real.pi)) *
          glyzDyadicScale q ^ (d + 1) →
      ∀ (g : Plane → ℂ), Integrable g → Function.support g ⊆ {y | y.2 ∈ Icc rmin rmax} →
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      let δ := glyzDyadicScale n
      let E := fun j => ∫⁻ x, ‖glyzRawExtension Φ a
        (glyzDyadicInput (n + q) (i * 2 ^ q + j) g) r x‖ₑ ^ (p : ℝ)
      (∫⁻ x, ‖glyzRawExtension Φ a (glyzDyadicInput n i g) r x‖ₑ ^ (p : ℝ)) ≤
        (m : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (((∑ l, (ENNReal.ofReal (b l))⁻¹ *
            glyzParabolicPowerCoefficient (d + 1) p ε (C l) (Cg l) q * ENNReal.ofReal (Cj l)) *
              ∑ j ∈ Finset.range (2 ^ q), E j) +
            (∑ l, (ENNReal.ofReal (b l))⁻¹ * (c l : ℝ≥0∞)⁻¹ *
              glyzParabolicErrorCoefficient (d + 1) W M p ε (C l) (D l) (L l) δ
                (r * δ ^ (d + 2)) q T) * (∫⁻ y, ‖glyzDyadicInput n i g y‖ₑ) ^ (p : ℝ)) := by
  classical
  have hΦ : ContDiff ℝ ∞ (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) :=
    hG.comp (contDiff_snd.prodMk contDiff_fst)
  have hp1 : (1 : ℝ) ≤ p := by
    exact_mod_cast (one_le_glyzCriticalNNExponent (by omega : 0 < d + 1)).trans hp
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨χ, τ, hτ, hχ, hcχ, hrχ, hχdet, hfreeze⟩ :=
    G.exists_glyz_frozen_time_cutoff hG hK hdet
  obtain ⟨S, ψ₀, σ₀, e₀, K₀, hatlas, hsum₀⟩ :=
    G.exists_glyz_smooth_moving_chart_partition hG χ hχ hcχ (fun x => (hrχ x).1)
      hχdet (m := d + 2) le_rfl
  let m := Fintype.card S
  let equivI : Fin m ≃ S := (Fintype.equivFin S).symm
  let ψ := fun l => ψ₀ (equivI l)
  let σ := fun l => σ₀ (equivI l)
  let e := fun l => e₀ (equivI l)
  let Kl := fun l => K₀ (equivI l)
  let v := fun l => (parameterFrame d).symm (equivI l).val.val.2
  have hsum (x : ℝ × Parameters 2 d) : ∑ l : Fin m, ψ l x = χ x := by
    rw [show (∑ l : Fin m, ψ l x) = ∑ l : S, ψ₀ l x from equivI.sum_comp (fun l => ψ₀ l x)]
    exact hsum₀ x
  have hlocal (l : Fin m) := by
    obtain ⟨_, _, _, _, hKi, hKS, he, hf, hi, _, _⟩ := hatlas (equivI l)
    have htarget : IsCompact (e l '' Kl l) :=
      hKi.image_of_continuousOn ((e l).continuousOn.mono hKS)
    have htargetSub : e l '' Kl l ⊆ (e l).target := by
      rintro _ ⟨z, hz, rfl⟩
      exact (e l).map_source (hKS hz)
    exact G.exists_glyz_raw_chart_parent_step (by omega : 0 < d + 1) le_rfl (σ l) (e l)
      he hf hi ha hΦ htarget htargetSub W M hW hp hε hrmin (rmax := rmax)
  choose ρ C D L Cg b Cj c hρ hcρ hrρ hρ1 hρT hC hD hL hCg hb hCj hcc hstep using hlocal
  refine ⟨τ, hτ, m, C, D, L, Cg, b, Cj, c,
    fun l => ⟨hC l, hD l, hL l, hCg l, hb l, hCj l, hcc l⟩, ?_⟩
  intro n q i r T hsmall hr hT hscale g hg hgs
  let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
  let δ := glyzDyadicScale n
  let s := glyzDyadicLeft n i
  let f := glyzDyadicInput n i g
  let fj := fun j => glyzDyadicInput (n + q) (i * 2 ^ q + j) g
  let gn := fun j => glyzNormalizedDyadicInput n q i j g
  let J := fun j => Icc (glyzDyadicLeft q j) (glyzDyadicRight q j)
  let F := glyzRawExtension Φ a f r
  let Fj := fun j => glyzRawExtension Φ a (fj j) r
  have hδ : 0 < δ := glyzDyadicScale_pos n
  have hδ1 : δ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hf : Integrable f := integrable_glyzDyadicInput hg n i
  have hF : Continuous F := (contDiff_glyzRawExtension hΦ ha hc hf r).continuous
  have hFj (j : ℕ) : Continuous (Fj j) :=
    (contDiff_glyzRawExtension hΦ ha hc (integrable_glyzDyadicInput hg _ _) r).continuous
  have hparent : Function.support f ⊆ Icc s (s + δ) ×ˢ Icc rmin rmax := by
    simpa [f, s, δ] using support_glyzDyadicInput_child_parent hgs n 0 i 0 (by norm_num)
  have hpart (x : Parameters 2 d) : ∑ l : Fin m, (ψ l (s, x) : ℂ) * F x = F x :=
    glyzRawExtension_frozen_partition Φ a f r s δ has
      (fun y hy => (hparent hy).1) χ ψ
      (fun x hx hdist => hfreeze x hx s (hdist.trans hsmall)) hsum x
  have hgn (j : ℕ) : Integrable (gn j) := integrable_glyzNormalizedDyadicInput hg n q i j
  have hgnt (j : ℕ) (hj : j ∈ Finset.range (2 ^ q)) :
      Function.support (gn j) ⊆ J j ×ˢ Icc rmin rmax := by
    intro y hy
    have hh := support_glyzNormalizedDyadicInput hgs n q i j hy
    exact ⟨⟨hh.1.1, hh.1.2.le⟩, hh.2⟩
  have hmass : δ * (∑ j ∈ Finset.range (2 ^ q), ∫ y, ‖gn j y‖) = ∫ y, ‖f y‖ := by
    rw [glyzNormalizedDyadicInput_integral_norm_sum hg n q i]
    dsimp [δ, f]
    rw [← mul_assoc, mul_inv_cancel₀ (glyzDyadicScale_pos n).ne', one_mul]
  let main := fun l => (ENNReal.ofReal (b l))⁻¹ *
    glyzParabolicPowerCoefficient (d + 1) p ε (C l) (Cg l) q * ENNReal.ofReal (Cj l)
  let err := fun l => (ENNReal.ofReal (b l))⁻¹ * (c l : ℝ≥0∞)⁻¹ *
    glyzParabolicErrorCoefficient (d + 1) W M p ε (C l) (D l) (L l) δ
      (r * δ ^ (d + 2)) q T
  have hpatch (l : Fin m) : (∫⁻ x, ‖(ψ l (s, x) : ℂ) * F x‖ₑ ^ (p : ℝ)) ≤
      main l * (∑ j ∈ Finset.range (2 ^ q), ∫⁻ x, ‖Fj j x‖ₑ ^ (p : ℝ)) +
      err l * (∫⁻ y, ‖f y‖ₑ) ^ (p : ℝ) := by
    obtain ⟨hψ, _, _, hrψ, _, hKS, he, _, _, _, hψK⟩ := hatlas (equivI l)
    have hfirst : ∀ x, (e l x).1 = x.1 := by
      intro x
      change (e₀ (equivI l) x).1 = x.1
      rw [he]
    have hdom := glyz_original_frozen_patch_power_le (σ l) (v l) s (e l) hfirst
      (ψ l) hψ.continuous (fun x => ⟨(hrψ x).1, (hrψ x).2.trans (hrχ x).2⟩)
      (ρ l) (Kl l) hKS hψK (fun z hz => hρ1 l _ ⟨z, hz, rfl⟩) F hF hp0
    have hdec := hstep l (s, v l) δ hδ hδ1 r q T hr hT hscale
      (Finset.range (2 ^ q)) J gn subset_rfl (fun _ => isCompact_Icc)
      (fun j hj => glyzDyadicInterval_subset_unit (Finset.mem_range.mp hj))
      (fun j _ t ht => glyzDyadicInterval_dist_center q j ht) hgn hgnt
    simp only [glyzRawChartExtension, gn, s, δ, glyzDenormalizedInput_normalizedDyadicInput] at hdec
    have hsumF (z : Aux (d + 2)) :
        (∑ j ∈ Finset.range (2 ^ q),
          (ρ l ((s, v l), (e l ((s, v l), z)).2) : ℂ) *
            Fj j (parameterFrame d (v l + coordinateInsertion (σ l) z))) =
        (ρ l ((s, v l), (e l ((s, v l), z)).2) : ℂ) *
          F (parameterFrame d (v l + coordinateInsertion (σ l) z)) := by
      rw [← Finset.mul_sum]
      congr 1
      exact (glyzRawExtension_dyadicInput_refine hΦ ha hc hg r n q i _).symm
    change (∫⁻ z in {z | ((s, v l), z) ∈ (e l).source}, ‖∑ j ∈ Finset.range (2 ^ q),
        (ρ l ((s, v l), (e l ((s, v l), z)).2) : ℂ) *
          Fj j (parameterFrame d (v l + coordinateInsertion (σ l) z))‖ₑ ^ (p : ℝ)) ≤ _ at hdec
    simp_rw [hsumF] at hdec
    have herr' : (ENNReal.ofReal (b l))⁻¹ *
        ((c l : ℝ≥0∞) * ENNReal.ofReal |∏ u : Fin (d + 2), δ ^ (u : ℕ) / δ ^ (d + 1)|)⁻¹ *
        ENNReal.ofReal δ ^ (p : ℝ) *
        glyzParabolicPowerError (d + 1) W M p ε (C l) (D l) (L l) δ
          (r * δ ^ (d + 2)) q T (Finset.range (2 ^ q)) gn ≤
        err l * (∫⁻ y, ‖f y‖ₑ) ^ (p : ℝ) := by
      rw [← ofReal_integral_norm_eq_lintegral_enorm hf]
      exact glyz_chart_parabolic_error_le (d + 1) W M p hp1 ε (C l) (D l) (L l)
        δ (r * δ ^ (d + 2)) (hD l) hδ hδ1 q T hT (Finset.range (2 ^ q)) gn
        (∫ y, ‖f y‖) (b l) (c l) hmass
    apply hdom.trans
    apply hdec.trans
    apply add_le_add _ herr'
    apply mul_le_mul_right
    apply Finset.sum_le_sum
    intro j hj
    exact glyz_original_chart_child_power_le (σ l) (v l) s (e l) (ρ l) (hrρ l) (Fj j) (hFj j) hp0.le
  have hm (l : Fin m) : Measurable (fun x => ‖(ψ l (s, x) : ℂ) * F x‖ₑ ^ (p : ℝ)) := by
    have hh : Continuous (fun x => ψ l (s, x)) :=
      (hatlas (equivI l)).1.continuous.comp (continuous_const.prodMk continuous_id)
    exact ((Complex.continuous_ofReal.comp hh).mul hF).measurable.enorm.pow_const _
  have hall := glyz_finite_output_patch_assembly volume F (fun l x => (ψ l (s, x) : ℂ)) hp1
    hpart hm main (fun l => err l * (∫⁻ y, ‖f y‖ₑ) ^ (p : ℝ))
      (∑ j ∈ Finset.range (2 ^ q), ∫⁻ x, ‖Fj j x‖ₑ ^ (p : ℝ)) hpatch
  rw [← Finset.sum_mul] at hall
  simpa only [Fintype.card_fin] using hall

end PlanarNikodym
