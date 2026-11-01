import PlanarNikodym.Analysis.Fourier.MicrolocalErrorUniform
import PlanarNikodym.Analysis.Fourier.OscillatoryFrequencyJets

/-! Exact frequency-jet factors and uniform nonstationary bounds for the
complete frequency jets. No local smoothing estimate is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace PlanarNikodym

/-- The full exponential derivative evaluated on arbitrary directions. -/
theorem iteratedFDeriv_cexp_clm_apply
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℂ) (n : ℕ) (x : E) (v : Fin n → E) :
    iteratedFDeriv ℝ n (fun y => Complex.exp (L y)) x v =
      Complex.exp (L x) * ∏ i, L (v i) := by
  let f : E → ℂ := fun y => Complex.exp (L y)
  have hf : ContDiff ℝ ∞ f := L.contDiff.cexp
  let M : ℂ →L[ℝ] (E →L[ℝ] ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ L).restrictScalars ℝ
  have hdf : fderiv ℝ f = M ∘ f := by
    funext y
    exact L.hasFDerivAt.cexp.fderiv
  change iteratedFDeriv ℝ n f x v = f x * ∏ i, L (v i)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedFDeriv_succ_apply_right]
    change iteratedFDeriv ℝ n (fderiv ℝ f) x (Fin.init v) (v (Fin.last n)) = _
    rw [hdf, M.iteratedFDeriv_comp_left (contDiff_infty.mp hf n).contDiffAt le_rfl]
    change (iteratedFDeriv ℝ n f x (Fin.init v)) * L (v (Fin.last n)) = _
    rw [ih]
    rw [Fin.prod_univ_castSucc]
    change (f x * ∏ i : Fin n, L (v i.castSucc)) * L (v (Fin.last n)) = _
    ring

def planeCoordinate (x : Plane) (i : Fin 2) : ℝ := if i = 0 then x.1 else x.2

def planeCoordinateBasis (i : Fin 2) : Plane := if i = 0 then (1, 0) else (0, 1)

theorem planeCoordinate_sum (x : Plane) :
    ∑ i : Fin 2, planeCoordinate x i • planeCoordinateBasis i = x := by
  simp [Fin.sum_univ_two, planeCoordinate, planeCoordinateBasis]

theorem abs_planeCoordinate_le (x : Plane) (i : Fin 2) :
    |planeCoordinate x i| ≤ ‖x‖ := by
  fin_cases i
  · simpa [planeCoordinate, Real.norm_eq_abs] using norm_fst_le x
  · simpa [planeCoordinate, Real.norm_eq_abs] using norm_snd_le x

/-- The product norm on `Plane` gives a direct finite-coordinate bound
for every complete multilinear map. -/
theorem norm_plane_multilinear_le_sum_basis {m : ℕ}
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : Plane [×m]→L[ℝ] F) :
    ‖T‖ ≤ ∑ σ : Fin m → Fin 2, ‖T (fun i => planeCoordinateBasis (σ i))‖ := by
  classical
  apply T.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro v
  have he : T v = ∑ σ : Fin m → Fin 2,
      (∏ i, planeCoordinate (v i) (σ i)) • T (fun i => planeCoordinateBasis (σ i)) := by
    calc
      T v = T (fun i => ∑ j : Fin 2, planeCoordinate (v i) j • planeCoordinateBasis j) := by
        congr 1
        funext i
        exact (planeCoordinate_sum (v i)).symm
      _ = ∑ σ : Fin m → Fin 2,
          T (fun i => planeCoordinate (v i) (σ i) • planeCoordinateBasis (σ i)) :=
        T.toMultilinearMap.map_sum _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro σ _
        exact T.toMultilinearMap.map_smul_univ _ _
  rw [he]
  calc
    _ ≤ ∑ σ : Fin m → Fin 2,
        ‖(∏ i, planeCoordinate (v i) (σ i)) • T (fun i => planeCoordinateBasis (σ i))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ σ : Fin m → Fin 2,
        (∏ i, ‖v i‖) * ‖T (fun i => planeCoordinateBasis (σ i))‖ := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod]
      gcongr
      exact abs_planeCoordinate_le _ _
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem fourierCharacterExponent_symm (x ξ : Plane) :
    fourierCharacterExponent x ξ = fourierCharacterExponent ξ x := by
  simp only [fourierCharacterExponent_apply]
  congr 3
  unfold fourierPhase
  ring

theorem iteratedFDeriv_planeFourierCharacter_frequency_apply
    (x ξ : Plane) (j : ℕ) (v : Fin j → Plane) :
    iteratedFDeriv ℝ j (fun η => planeFourierCharacter x η) ξ v =
      planeFourierCharacter x ξ * ∏ i, fourierCharacterExponent (v i) x := by
  have he : (fun η => Complex.exp (fourierCharacterExponent x η)) =
      fun η => planeFourierCharacter x η := by
    funext η
    rw [fourierCharacterExponent_apply, planeFourierCharacter_symm x η]
    rfl
  have h := iteratedFDeriv_cexp_clm_apply (fourierCharacterExponent x) j ξ v
  rw [he, show Complex.exp (fourierCharacterExponent x ξ) = planeFourierCharacter x ξ from
    congrFun he ξ] at h
  simpa only [fourierCharacterExponent_symm x] using h

theorem Family.cutoffOscillatoryAmplitude_frequency_jet_apply_eq_integral
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (q : Parameters 2 d) (j : ℕ) (ξ : Plane) (v : Fin j → Plane) :
    iteratedFDeriv ℝ j (G.cutoffOscillatoryAmplitude χ q) ξ v =
      ∫ t : ℝ, (χ (t, q) : ℂ) * planeFourierCharacter (G.graphMap q t) ξ *
        ∏ i, fourierCharacterExponent (v i) (G.graphMap q t) := by
  rw [G.cutoffOscillatoryAmplitude_frequency_jet_eq_integral χ hχ hc hγ q j ξ,
    ContinuousMultilinearMap.integral_apply
      (G.cutoffOscillatoryFrequencyJet_integrable χ hχ hc hγ q j ξ) v]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [ContinuousMultilinearMap.smul_apply,
    iteratedFDeriv_planeFourierCharacter_frequency_apply]
  change (χ (t, q) : ℂ) * (_ * _) = _
  ring

def Family.microlocalFrequencyJetAmplitude {d j : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (a : Plane → ℝ) (v : Fin j → Plane)
    (x : (Parameters 2 d × Plane) × ℝ) : ℂ :=
  microlocalJointAmplitude χ a x *
    ∏ i, fourierCharacterExponent (v i) (G.graphMap x.1.1 x.2)

theorem Family.tsupport_microlocalFrequencyJetAmplitude_subset {d j : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (a : Plane → ℝ) (v : Fin j → Plane) :
    tsupport (G.microlocalFrequencyJetAmplitude χ a v) ⊆
      tsupport (microlocalJointAmplitude χ a) :=
  tsupport_mul_subset_left

theorem Family.contDiff_microlocalFrequencyJetAmplitude {d j : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (a : Plane → ℝ) (v : Fin j → Plane)
    (hχ : ContDiff ℝ ∞ χ) (ha : ContDiff ℝ ∞ a)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x) :
    ContDiff ℝ ∞ (G.microlocalFrequencyJetAmplitude χ a v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : (x.2, x.1.1) ∈ tsupport χ
  · have hg : ContDiffAt ℝ ∞
        (fun y : (Parameters 2 d × Plane) × ℝ => G.graphMap y.1.1 y.2) x :=
      contDiffAt_snd.prodMk ((hγ (x.2, x.1.1) hx).comp x
        (f := fun y : (Parameters 2 d × Plane) × ℝ => (y.2, y.1.1))
        (contDiffAt_snd.prodMk contDiffAt_fst.fst))
    apply (contDiff_microlocalJointAmplitude hχ ha).contDiffAt.mul
    apply contDiffAt_prod
    intro i _
    exact (fourierCharacterExponent (v i)).contDiff.contDiffAt.comp x hg
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    have he : ∀ᶠ y in 𝓝 x, (y.2, y.1.1) ∉ tsupport χ :=
      (continuous_snd.prodMk continuous_fst.fst).continuousAt.eventually
        ((isClosed_tsupport χ).isOpen_compl.mem_nhds hx)
    filter_upwards [he] with y hy
    simp only [Family.microlocalFrequencyJetAmplitude, microlocalJointAmplitude,
      image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_mul]

theorem Family.hasCompactSupport_microlocalFrequencyJetAmplitude {d j : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (a : Plane → ℝ) (v : Fin j → Plane)
    (hcχ : HasCompactSupport χ) (hca : HasCompactSupport a) :
    HasCompactSupport (G.microlocalFrequencyJetAmplitude χ a v) :=
  (hasCompactSupport_microlocalJointAmplitude hcχ hca).of_isClosed_subset
    (isClosed_tsupport _) (G.tsupport_microlocalFrequencyJetAmplitude_subset χ a v)

/-- Nonstationary integration by parts controls every fixed complete-jet
component; its constant is uniform in all curve parameters and frequencies. -/
theorem Family.exists_uniform_cutoffOscillatoryAmplitude_frequency_component_decay
    {d j : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (a : Plane → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (hne : ∀ ξ ∈ tsupport a, ∀ x ∈ tsupport χ,
      deriv (G.graphPhase x.2 ξ) x.1 ≠ 0)
    (v : Fin j → Plane) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Parameters 2 d) (ξ : Plane) (r : ℝ), r ≠ 0 →
      ‖(a ξ : ℂ) * iteratedFDeriv ℝ j
        (fun η => G.cutoffOscillatoryAmplitude χ q (r • η)) ξ v‖ ≤
        C * (|r|⁻¹) ^ n := by
  let b := G.microlocalFrequencyJetAmplitude χ a v
  let Φ : (Parameters 2 d × Plane) × ℝ → ℝ :=
    fun x => G.normalizedGraphPhase x.1.1 x.1.2 x.2
  have hb : ContDiff ℝ ∞ b := G.contDiff_microlocalFrequencyJetAmplitude χ a v hχ ha hγ
  have hcb : HasCompactSupport b := G.hasCompactSupport_microlocalFrequencyJetAmplitude χ a v hcχ hca
  have hs (x) (hx : x ∈ tsupport b) :
      (x.2, x.1.1) ∈ tsupport χ ∧ x.1.2 ∈ tsupport a :=
    microlocalJointAmplitude_tsupport_subset χ a
      (G.tsupport_microlocalFrequencyJetAmplitude_subset χ a v hx)
  have hΦ : ∀ x ∈ tsupport b, ContDiffAt ℝ ∞ Φ x := by
    intro x hx
    have hg : ContDiffAt ℝ ∞
        (fun y : (Parameters 2 d × Plane) × ℝ => G.γ y.2 y.1.1) x :=
      (hγ (x.2, x.1.1) (hs x hx).1).comp x
        (f := fun y : (Parameters 2 d × Plane) × ℝ => (y.2, y.1.1))
        (contDiffAt_snd.prodMk contDiffAt_fst.fst)
    exact contDiffAt_const.mul
      ((contDiffAt_snd.mul contDiffAt_fst.snd.fst).add (hg.mul contDiffAt_fst.snd.snd))
  have hΦne : ∀ x ∈ tsupport b, partialTimeDeriv Φ x ≠ 0 := by
    intro x hx
    obtain ⟨hxχ, hxa⟩ := hs x hx
    have hp := (G.contDiffAt_graphPhase (hγ (x.2, x.1.1) hxχ) x.1.2).differentiableAt (by simp)
    change deriv (G.normalizedGraphPhase x.1.1 x.1.2) x.2 ≠ 0
    rw [show deriv (G.normalizedGraphPhase x.1.1 x.1.2) x.2 =
        (2 * Real.pi) * deriv (G.graphPhase x.1.1 x.1.2) x.2 from
      (hp.hasDerivAt.const_mul (2 * Real.pi)).deriv]
    exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
      (hne x.1.2 hxa (x.2, x.1.1) hxχ)
  obtain ⟨C, hC, hbound⟩ := exists_uniform_nonstationary_decay_constant hΦ hb hcb hΦne (n + j)
  refine ⟨C, hC, ?_⟩
  intro q ξ r hr
  have hd := congrFun (iteratedFDeriv_comp_const_smul r
    (contDiff_infty.mp (G.cutoffOscillatoryAmplitude_frequency_contDiff χ hχ hcχ hγ q) j)) ξ
  have he : (a ξ : ℂ) * iteratedFDeriv ℝ j
      (fun η => G.cutoffOscillatoryAmplitude χ q (r • η)) ξ v =
      r ^ j • ∫ t : ℝ, phaseOscillation (fun s => Φ ((q, ξ), s)) r t * b ((q, ξ), t) := by
    rw [hd, ContinuousMultilinearMap.smul_apply,
      G.cutoffOscillatoryAmplitude_frequency_jet_apply_eq_integral χ hχ hcχ hγ q j (r • ξ) v]
    change (a ξ : ℂ) • ((r ^ j : ℝ) • (_ : ℂ)) = (r ^ j : ℝ) • (_ : ℂ)
    rw [smul_comm]
    congr 1
    change (a ξ : ℂ) * (∫ t : ℝ, _) = _
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [G.planeFourierCharacter_eq_phaseOscillation]
    dsimp only [b, Family.microlocalFrequencyJetAmplitude, microlocalJointAmplitude, Φ]
    ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_pow]
  have hcancel : |r| ^ j * (|r|⁻¹) ^ (n + j) = (|r|⁻¹) ^ n := by
    rw [pow_add]
    calc
      _ = (|r|⁻¹) ^ n * (|r| * |r|⁻¹) ^ j := by rw [mul_pow]; ring
      _ = _ := by rw [mul_inv_cancel₀ (abs_ne_zero.mpr hr), one_pow, mul_one]
  calc
    _ ≤ |r| ^ j * (C * (|r|⁻¹) ^ (n + j)) :=
      mul_le_mul_of_nonneg_left (hbound (q, ξ) r hr) (by positivity)
    _ = C * (|r|⁻¹) ^ n := by rw [mul_left_comm, hcancel]

/-- Arbitrary-order rapid decay of the entire multilinear frequency jet,
after multiplication by the true compact nonstationary symbol. -/
theorem Family.exists_uniform_cutoffOscillatoryAmplitude_frequency_jet_decay
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (a : Plane → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (hne : ∀ ξ ∈ tsupport a, ∀ x ∈ tsupport χ,
      deriv (G.graphPhase x.2 ξ) x.1 ≠ 0) (j n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Parameters 2 d) (ξ : Plane) (r : ℝ), r ≠ 0 →
      ‖(a ξ : ℂ) • iteratedFDeriv ℝ j
        (fun η => G.cutoffOscillatoryAmplitude χ q (r • η)) ξ‖ ≤
        C * (|r|⁻¹) ^ n := by
  classical
  have hb (σ : Fin j → Fin 2) :=
    G.exists_uniform_cutoffOscillatoryAmplitude_frequency_component_decay χ hχ hcχ hγ a ha hca hne
      (fun i => planeCoordinateBasis (σ i)) n
  choose C hC hbound using hb
  refine ⟨∑ σ, C σ, Finset.sum_nonneg (fun σ _ => hC σ), ?_⟩
  intro q ξ r hr
  calc
    _ ≤ ∑ σ : Fin j → Fin 2, ‖((a ξ : ℂ) • iteratedFDeriv ℝ j
        (fun η => G.cutoffOscillatoryAmplitude χ q (r • η)) ξ)
          (fun i => planeCoordinateBasis (σ i))‖ := norm_plane_multilinear_le_sum_basis _
    _ ≤ ∑ σ : Fin j → Fin 2, C σ * (|r|⁻¹) ^ n := by
      apply Finset.sum_le_sum
      intro σ _
      exact hbound σ q ξ r hr
    _ = _ := (Finset.sum_mul _ _ _).symm

def planeJetComponent {i : ℕ} (a : Plane → ℝ) (σ : Fin i → Fin 2) (ξ : Plane) : ℝ :=
  iteratedFDeriv ℝ i a ξ (fun k => planeCoordinateBasis (σ k))

theorem contDiff_planeJetComponent {i : ℕ} {a : Plane → ℝ}
    (ha : ContDiff ℝ ∞ a) (σ : Fin i → Fin 2) :
    ContDiff ℝ ∞ (planeJetComponent a σ) := by
  let ev : (Plane [×i]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    { toFun := fun T => T (fun k => planeCoordinateBasis (σ k))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      cont := continuous_eval_const _ }
  have hJ : ContDiff ℝ ∞ (iteratedFDeriv ℝ i a) :=
    (contDiff_parameter_iteratedFDeriv i
      (ha.comp (contDiff_fst : ContDiff ℝ ∞ (fun x : Plane × ℝ => x.1)))).comp
      (contDiff_id.prodMk (contDiff_const (c := (0 : ℝ))))
  exact ev.contDiff.comp hJ

theorem tsupport_planeJetComponent_subset {i : ℕ} (a : Plane → ℝ) (σ : Fin i → Fin 2) :
    tsupport (planeJetComponent a σ) ⊆ tsupport a := by
  exact (tsupport_comp_subset
    (g := fun T : Plane [×i]→L[ℝ] ℝ => T (fun k => planeCoordinateBasis (σ k))) rfl
    (iteratedFDeriv ℝ i a)).trans (tsupport_iteratedFDeriv_subset i)

theorem hasCompactSupport_planeJetComponent {i : ℕ} {a : Plane → ℝ}
    (hca : HasCompactSupport a) (σ : Fin i → Fin 2) :
    HasCompactSupport (planeJetComponent a σ) :=
  hca.of_isClosed_subset (isClosed_tsupport _) (tsupport_planeJetComponent_subset a σ)

/-- Each Leibniz factor is rapidly decreasing: the real components of
every symbol derivative remain compact and nonstationary. -/
theorem Family.exists_uniform_symbolJet_mul_amplitudeJet_decay
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (a : Plane → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (hne : ∀ ξ ∈ tsupport a, ∀ x ∈ tsupport χ,
      deriv (G.graphPhase x.2 ξ) x.1 ≠ 0) (i j n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Parameters 2 d) (ξ : Plane) (r : ℝ), r ≠ 0 →
      ‖iteratedFDeriv ℝ i a ξ‖ *
        ‖iteratedFDeriv ℝ j (fun η => G.cutoffOscillatoryAmplitude χ q (r • η)) ξ‖ ≤
        C * (|r|⁻¹) ^ n := by
  classical
  have hb (σ : Fin i → Fin 2) :=
    G.exists_uniform_cutoffOscillatoryAmplitude_frequency_jet_decay χ hχ hcχ hγ
      (planeJetComponent a σ) (contDiff_planeJetComponent ha σ)
      (hasCompactSupport_planeJetComponent hca σ)
      (fun ξ hξ => hne ξ (tsupport_planeJetComponent_subset a σ hξ)) j n
  choose C hC hbound using hb
  refine ⟨∑ σ, C σ, Finset.sum_nonneg (fun σ _ => hC σ), ?_⟩
  intro q ξ r hr
  calc
    _ ≤ (∑ σ : Fin i → Fin 2, |planeJetComponent a σ ξ|) *
        ‖iteratedFDeriv ℝ j (fun η => G.cutoffOscillatoryAmplitude χ q (r • η)) ξ‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [planeJetComponent, Real.norm_eq_abs] using
        norm_plane_multilinear_le_sum_basis (iteratedFDeriv ℝ i a ξ)
    _ = ∑ σ : Fin i → Fin 2, ‖(planeJetComponent a σ ξ : ℂ) • iteratedFDeriv ℝ j
        (fun η => G.cutoffOscillatoryAmplitude χ q (r • η)) ξ‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ σ : Fin i → Fin 2, C σ * (|r|⁻¹) ^ n := by
      apply Finset.sum_le_sum
      intro σ _
      exact hbound σ q ξ r hr
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Every complete frequency derivative of the actual compact-symbol
error is rapidly decreasing, uniformly in parameters and normalized
frequencies. The frequency scale can be any nonzero real number. -/
theorem Family.exists_uniform_cutoffOscillatoryAmplitude_symbol_frequency_jet_decay
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (a : Plane → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (hne : ∀ ξ ∈ tsupport a, ∀ x ∈ tsupport χ,
      deriv (G.graphPhase x.2 ξ) x.1 ≠ 0) (j n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Parameters 2 d) (ξ : Plane) (r : ℝ), r ≠ 0 →
      ‖iteratedFDeriv ℝ j (fun η => (a η : ℂ) *
        G.cutoffOscillatoryAmplitude χ q (r • η)) ξ‖ ≤ C * (|r|⁻¹) ^ n := by
  have hb (i : ℕ) := G.exists_uniform_symbolJet_mul_amplitudeJet_decay
    χ hχ hcχ hγ a ha hca hne i (j - i) n
  choose C hC hbound using hb
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * C i,
    Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hC i)), ?_⟩
  intro q ξ r hr
  have hscaled : ContDiff ℝ ∞ (fun η => G.cutoffOscillatoryAmplitude χ q (r • η)) :=
    (G.cutoffOscillatoryAmplitude_frequency_contDiff χ hχ hcχ hγ q).comp
      (contDiff_id.const_smul r)
  have hle := norm_iteratedFDeriv_smul_le (contDiff_infty.mp ha j)
    (contDiff_infty.mp hscaled j) ξ (n := j) le_rfl
  change ‖iteratedFDeriv ℝ j (fun η => (a η : ℂ) *
    G.cutoffOscillatoryAmplitude χ q (r • η)) ξ‖ ≤ _ at hle
  apply hle.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (C i * (|r|⁻¹) ^ n) := by
      apply Finset.sum_le_sum
      intro i _
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hbound i q ξ r hr) (Nat.cast_nonneg _)
    _ = _ := by simp_rw [← mul_assoc]; exact (Finset.sum_mul _ _ _).symm

theorem Family.contDiff_symbol_cutoffOscillatoryAmplitude_frequency
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {a : Plane → ℝ} (ha : ContDiff ℝ ∞ a) (q : Parameters 2 d) (r : ℝ) :
    ContDiff ℝ ∞ (fun η => (a η : ℂ) * G.cutoffOscillatoryAmplitude χ q (r • η)) :=
  (Complex.ofRealCLM.contDiff.comp ha).mul
    ((G.cutoffOscillatoryAmplitude_frequency_contDiff χ hχ hcχ hγ q).comp
      (contDiff_id.const_smul r))

theorem Family.tsupport_symbol_cutoffOscillatoryAmplitude_frequency_subset
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d) (a : Plane → ℝ)
    (q : Parameters 2 d) (r : ℝ) :
    tsupport (fun η => (a η : ℂ) * G.cutoffOscillatoryAmplitude χ q (r • η)) ⊆ tsupport a :=
  tsupport_mul_subset_left.trans (tsupport_comp_subset (g := Complex.ofRealCLM) rfl a)

theorem Family.hasCompactSupport_symbol_cutoffOscillatoryAmplitude_frequency
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d) {a : Plane → ℝ}
    (hca : HasCompactSupport a) (q : Parameters 2 d) (r : ℝ) :
    HasCompactSupport (fun η => (a η : ℂ) * G.cutoffOscillatoryAmplitude χ q (r • η)) :=
  hca.of_isClosed_subset (isClosed_tsupport _)
    (G.tsupport_symbol_cutoffOscillatoryAmplitude_frequency_subset χ a q r)

/-- One genuinely constructed microlocal split has rapid bounds for
every complete frequency derivative and every desired decay order. -/
theorem Family.exists_microlocal_error_uniform_frequency_jet_decay
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) :
    ∃ (δ : ℝ) (β : ℝ → ℝ), 0 < δ ∧ δ ≤ 1 / 4 ∧ ContDiff ℝ ∞ β ∧
      (∀ s, |s| ≤ δ / 2 → β s = 0) ∧ (∀ s, δ ≤ |s| → β s = 1) ∧
      HasCompactSupport (fun ξ : Plane => L.bandSymbol 0 ξ * (1 - β ξ.2)) ∧
      ∀ (j n : ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ (q : Parameters 2 d) (ξ : Plane) (r : ℝ), r ≠ 0 →
          ‖iteratedFDeriv ℝ j (fun η =>
            ((L.bandSymbol 0 η * (1 - β η.2) : ℝ) : ℂ) *
              G.cutoffOscillatoryAmplitude χ q (r • η)) ξ‖ ≤ C * (|r|⁻¹) ^ n := by
  obtain ⟨δ, β, hδ, hδle, hβ, _, hβzero, hβone, _, herror, _, hnonstat⟩ :=
    G.exists_microlocal_band_split χ hcχ hγ L
  refine ⟨δ, β, hδ, hδle, hβ, hβzero, hβone, herror, ?_⟩
  intro j n
  apply G.exists_uniform_cutoffOscillatoryAmplitude_symbol_frequency_jet_decay
    χ hχ hcχ hγ _
    ((L.bandSymbol_smooth 0).mul (contDiff_const.sub (hβ.comp contDiff_snd))) herror _ j n
  intro ξ hξ x hx
  have h := hnonstat ξ hξ x hx
  intro hz
  simp only [hz, abs_zero] at h
  linarith

/-- The actual compact-symbol error, packaged without altering its
frequency function. The scale may be any real number. -/
def Family.cutoffOscillatoryErrorSchwartz {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (a : Plane → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (q : Parameters 2 d) (r : ℝ) : SchwartzMap Plane ℂ :=
  (G.hasCompactSupport_symbol_cutoffOscillatoryAmplitude_frequency χ hca q r).toSchwartzMap
    (G.contDiff_symbol_cutoffOscillatoryAmplitude_frequency χ hχ hcχ hγ ha q r)

@[simp] theorem Family.cutoffOscillatoryErrorSchwartz_apply {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (a : Plane → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (q : Parameters 2 d) (r : ℝ) (ξ : Plane) :
    G.cutoffOscillatoryErrorSchwartz χ hχ hcχ hγ a ha hca q r ξ =
      (a ξ : ℂ) * G.cutoffOscillatoryAmplitude χ q (r • ξ) := rfl

theorem Family.cutoffOscillatoryErrorSchwartz_coe {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (a : Plane → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (q : Parameters 2 d) (r : ℝ) :
    ⇑(G.cutoffOscillatoryErrorSchwartz χ hχ hcχ hγ a ha hca q r) =
      fun ξ => (a ξ : ℂ) * G.cutoffOscillatoryAmplitude χ q (r • ξ) := rfl

theorem Family.tsupport_cutoffOscillatoryErrorSchwartz_subset {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (a : Plane → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (q : Parameters 2 d) (r : ℝ) :
    tsupport (G.cutoffOscillatoryErrorSchwartz χ hχ hcχ hγ a ha hca q r) ⊆ tsupport a :=
  G.tsupport_symbol_cutoffOscillatoryAmplitude_frequency_subset χ a q r

/-- A parameter outside the true compact projection has identically
zero cutoff slice, hence identically zero Fourier amplitude. -/
theorem Family.cutoffOscillatoryAmplitude_eq_zero_off_parameter_support
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d) {q : Parameters 2 d}
    (hq : q ∉ Prod.snd '' tsupport χ) (ξ : Plane) :
    G.cutoffOscillatoryAmplitude χ q ξ = 0 := by
  have hz (t : ℝ) : χ (t, q) = 0 := image_eq_zero_of_notMem_tsupport
    (fun ht => hq ⟨(t, q), ht, rfl⟩)
  simp only [Family.cutoffOscillatoryAmplitude, hz, Complex.ofReal_zero, zero_mul, integral_zero]

theorem Family.cutoffOscillatoryErrorSchwartz_eq_zero_off_parameter_support
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (a : Plane → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    {q : Parameters 2 d} (hq : q ∉ Prod.snd '' tsupport χ) (r : ℝ) :
    G.cutoffOscillatoryErrorSchwartz χ hχ hcχ hγ a ha hca q r = 0 := by
  ext ξ
  simp only [Family.cutoffOscillatoryErrorSchwartz_apply,
    G.cutoffOscillatoryAmplitude_eq_zero_off_parameter_support χ hq, mul_zero,
    zero_apply]

/-- Both the physical parameter support and the normalized frequency
support are fixed independently of the scale. -/
theorem Family.tsupport_cutoffOscillatoryErrorSchwartz_parameters_subset
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (a : Plane → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a) (r : ℝ) :
    tsupport (fun q => G.cutoffOscillatoryErrorSchwartz χ hχ hcχ hγ a ha hca q r) ⊆
      Prod.snd '' tsupport χ := by
  apply closure_minimal ?_ (hcχ.isCompact.image continuous_snd).isClosed
  intro q hq
  by_contra h
  exact hq (G.cutoffOscillatoryErrorSchwartz_eq_zero_off_parameter_support χ hχ hcχ hγ a ha hca h r)

end PlanarNikodym
