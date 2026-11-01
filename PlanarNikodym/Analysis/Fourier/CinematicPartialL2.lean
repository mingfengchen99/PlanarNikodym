import PlanarNikodym.Analysis.Fourier.CinematicPartialFIO
import PlanarNikodym.Analysis.Fourier.SmallCinematicMainL2Norm

/-! The sharp half-derivative L2 gain of the actual partial Fourier main
term. Full FIO decay, the original r² factor and partial Plancherel are
combined with their exact powers. Signed cutoffs and all auxiliary
dimensions are allowed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace PlanarNikodym

theorem cinematic_partial_L2_scaling {M r : ℝ} (hM : 0 ≤ M) (hr : 0 < r) :
    r^2 * (2*Real.pi*r)⁻¹ * (M^2*r⁻¹^3)^(1/2 : ℝ) =
      ((2*Real.pi)⁻¹*M) * r^(-(1/2 : ℝ)) := by
  have hMs : (M^2)^(1/2 : ℝ) = M := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hM]
    norm_num
  have hrs : (r⁻¹^3)^(1/2 : ℝ) = r^(-(3/2 : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (inv_nonneg.mpr hr.le),
      Real.inv_rpow hr.le,← Real.rpow_neg hr.le]
    norm_num
  rw [Real.mul_rpow (sq_nonneg M) (pow_nonneg (inv_nonneg.mpr hr.le) 3),hMs,hrs]
  have hrr : r^2*r⁻¹*r^(-(3/2 : ℝ)) = r^(-(1/2 : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_neg_one,← Real.rpow_add hr,
      ← Real.rpow_add hr]
    norm_num
  calc
    _ = ((2*Real.pi)⁻¹*M) * (r^2*r⁻¹*r^(-(3/2 : ℝ))) := by rw [mul_inv_rev]; ring
    _ = _ := by rw [hrr]

theorem Family.exists_cinematic_partial_main_L2 {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    {κ : ℝ} (hκ : 0 < κ) (hgap : ∀ η : ℝ, |η| < κ → β η = 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ, 0 < r → ∀ f : Plane → ℂ,
      Integrable f → MemLp f 2 volume →
      eLpNorm (G.cutoffPartialExtension χ L β r f) 2 volume ≤
        C * ENNReal.ofReal (r^(-(1/2 : ℝ))) * eLpNorm f 2 volume := by
  let m : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * β ξ.2
  have hm : Continuous m := (L.bandSymbol_smooth 0).continuous.mul (hβ.continuous.comp continuous_snd)
  have hmc : HasCompactSupport m := (L.bandSymbol_compact 0).mul_right
  have hv : Prod.snd '' tsupport m ⊆ {η : ℝ | η ≠ 0} := by
    rintro η ⟨ξ,hξ,rfl⟩ he
    have hn : {ζ : Plane | |ζ.2| < κ} ∈ nhds ξ :=
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const).mem_nhds
        (by simpa [he] using hκ)
    have hnot : ξ ∉ tsupport m := by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [hn] with ζ hζ
      simp [m,hgap ζ.2 hζ]
    exact hnot hξ
  obtain ⟨ρ,N,hρ,hcρ,_hρb,_hN,hKN,hρ1,hρs⟩ := exists_compact_smooth_cutoff
    (hmc.isCompact.image continuous_snd) (isOpen_ne_fun continuous_id continuous_const) hv
  let a := partialDataAmplitude χ ρ
  have ha : ContDiff ℝ ∞ a := contDiff_partialDataAmplitude hχ hρ
  have hac : HasCompactSupport a := hasCompactSupport_partialDataAmplitude hc hcρ
  obtain ⟨C,hC,hfio⟩ := G.exists_cinematic_full_fio_L2_bound hG ha hac
    (fun z hz => hdet _ (partialDataAmplitude_tsupport_subset χ ρ hz).1)
    (fun z hz => hρs (partialDataAmplitude_tsupport_subset χ ρ hz).2)
  obtain ⟨M₀,hM₀⟩ := hmc.exists_bound_of_continuous hm
  let M : ℝ := |M₀|+1
  have hM : 0 ≤ M := by positivity
  have hb (ξ : Plane) : |m ξ| ≤ M := by
    have hb₀ : |m ξ| ≤ M₀ := by simpa only [Real.norm_eq_abs] using hM₀ ξ
    exact hb₀.trans (by dsimp [M]; linarith [le_abs_self M₀])
  let D : ℝ := (2*Real.pi)⁻¹*M
  have hD : 0 ≤ D := mul_nonneg (inv_nonneg.mpr (by positivity)) hM
  refine ⟨C*ENNReal.ofReal D, ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top,?_⟩
  intro r hr f hf hf2
  let g : Plane → ℂ := fun x => weightedPartialFourierData m f r x.1 x.2
  have hgnorm := cinematic_main_L2_norm_of_square volume volume g f
    (by positivity : 0 ≤ M^2*r⁻¹^3)
    (lintegral_weightedPartialFourierData_sq_le_of_integrable hm hmc hf hf2 hr hb)
  have hfreq : 0 < 2*Real.pi*r := by positivity
  have hF := hfio (2*Real.pi*r) hfreq g
    (continuous_weightedPartialFourierData hm hmc hf r)
  have heq : G.cutoffPartialExtension χ L β r f = r^2 •
      e2FullFIOIntegral (2*Real.pi*r) (fun q x => x.2*G.γ x.1 q) a g := by
    funext q
    exact G.cutoffPartialExtension_eq_fullFIO hG χ hχ hc L β hβ ρ hρ hcρ
      (fun η hη => hρ1 η (hKN hη)) r hf q
  rw [heq,eLpNorm_const_smul,← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
  calc
    _ ≤ ENNReal.ofReal (r^2) *
        (C * ENNReal.ofReal (2*Real.pi*r)⁻¹ *
          (ENNReal.ofReal ((M^2*r⁻¹^3)^(1/2 : ℝ)) * eLpNorm f 2 volume)) :=
      mul_le_mul_right (hF.trans (mul_le_mul_right hgnorm _)) _
    _ = _ := by
      have hs : ENNReal.ofReal (r^2) * ENNReal.ofReal (2*Real.pi*r)⁻¹ *
          ENNReal.ofReal ((M^2*r⁻¹^3)^(1/2 : ℝ)) =
            ENNReal.ofReal D * ENNReal.ofReal (r^(-(1/2 : ℝ))) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg r),
          ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg r) (inv_nonneg.mpr hfreq.le)),
          cinematic_partial_L2_scaling hM hr, ENNReal.ofReal_mul hD]
      calc
        _ = C * (ENNReal.ofReal (r^2) * ENNReal.ofReal (2*Real.pi*r)⁻¹ *
            ENNReal.ofReal ((M^2*r⁻¹^3)^(1/2 : ℝ))) * eLpNorm f 2 volume := by ac_rfl
        _ = _ := by rw [hs]; ac_rfl

end PlanarNikodym
