import PlanarNikodym.Analysis.Fourier.TimeSliceExtension
import PlanarNikodym.Analysis.Localization.ScaleTimeLocalization

/-! The finite geometric partition acts on the actual partial-Fourier
main term. Absolute integrability justifies both finite summation and
the order of time/frequency integration. -/
noncomputable section
open Set MeasureTheory
open scoped Classical ContDiff
namespace PlanarNikodym

theorem Family.cutoffPartialExtension_sum_cutoff {d : ℕ} {ι : Type*} [Fintype ι]
    (G : Family 2 d) (ψ : ι → Cutoff d) (hψ : ∀ i, Continuous (ψ i))
    (hc : ∀ i, HasCompactSupport (ψ i))
    (hγ : ∀ i x, x ∈ tsupport (ψ i) →
      ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) {β : ℝ → ℝ} (hβ : Continuous β)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) (q : Parameters 2 d) :
    G.cutoffPartialExtension (fun x => ∑ i, ψ i x) L β r f q =
      ∑ i, G.cutoffPartialExtension (ψ i) L β r f q := by
  let m : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * β ξ.2
  have hm : Continuous m := (L.bandSymbol_smooth 0).continuous.mul (hβ.comp continuous_snd)
  have hcm : HasCompactSupport m := (L.bandSymbol_compact 0).mul_right
  let F : ι → Plane → ℂ := fun i x => (ψ i (x.1, q) : ℂ) *
    weightedPartialFourierData m f r x.1 x.2 * oneDimFourierCharacter r (G.γ x.1 q) x.2
  have hF (i : ι) : Integrable (F i) (volume.prod volume) :=
    G.integrable_partialFourierExtension (ψ i) (hψ i) (hc i) (hγ i)
      (weighted_scaledFourierData_continuous hm hf r)
      (weighted_scaledFourierData_integrable hm hcm hf r) q r
  have hsum : Integrable (fun x => ∑ i, F i x) (volume.prod volume) :=
    integrable_finsetSum Finset.univ (fun i _ => hF i)
  unfold Family.cutoffPartialExtension
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  change r ^ 2 • (∫ η : ℝ, ∫ t : ℝ, ∑ i, F i (t, η)) =
    ∑ i, r ^ 2 • ∫ η : ℝ, ∫ t : ℝ, F i (t, η)
  rw [← integral_prod_symm _ hsum, integral_finsetSum Finset.univ (fun i _ => hF i), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_prod_symm _ (hF i)]

theorem Family.cutoffPartialExtension_scaleTimeLocalized {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (L : FrequencyCutoff) (β : ℝ → ℝ)
    (r a : ℝ) {δ : ℝ} (hδ : δ ≠ 0) (i : ℕ) (f : Plane → ℂ) (q : Parameters 2 d) :
    G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ a δ i) L β r f q =
      r ^ 2 • timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
        (fun x => (χ (x.2.1, x.1) : ℂ))
        (fun x => weightedPartialFourierData (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2)
          f r x.1 x.2) (2 * Real.pi * r) (a + (i : ℝ) * δ) δ q := by
  have he : scaleTimeLocalizedCutoff χ a δ i =
      fun x => χ x * timePartitionWindow ((x.1 - (a + (i : ℝ) * δ)) / δ) := by
    funext x
    unfold scaleTimeLocalizedCutoff scaleTimeCutoff
    congr 2
    field_simp
    ring
  rw [he]
  exact G.cutoffPartialExtension_timeSlice χ L β r _ δ f q

theorem Family.exists_cutoffPartialExtension_time_partition {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) {β : ℝ → ℝ} (hβ : Continuous β) {f : Plane → ℂ} (hf : Integrable f)
    (a b : ℝ) (hs : ∀ x ∈ tsupport χ, x.1 ∈ Icc a b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ r : ℝ, ∀ q : Parameters 2 d,
      G.cutoffPartialExtension χ L β r f q = ∑ i : Fin N,
        G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ a δ i) L β r f q := by
  obtain ⟨N, hN⟩ := exists_scaleTimeCutoff_partition a b hδ
  refine ⟨N, ?_⟩
  intro r q
  have he : (fun x => ∑ i : Fin N, scaleTimeLocalizedCutoff χ a δ i x) = χ := by
    funext x
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => scaleTimeLocalizedCutoff χ a δ i x) N]
    exact sum_scaleTimeLocalizedCutoff χ a b hδ N hN
      (fun x hx => hs x (subset_closure hx)) x
  calc
    _ = G.cutoffPartialExtension (fun x => ∑ i : Fin N, scaleTimeLocalizedCutoff χ a δ i x) L β r f q :=
      congrArg (fun ψ => G.cutoffPartialExtension ψ L β r f q) he.symm
    _ = _ := G.cutoffPartialExtension_sum_cutoff (fun i : Fin N => scaleTimeLocalizedCutoff χ a δ i)
      (fun i => (contDiff_scaleTimeLocalizedCutoff hχ a δ i).continuous)
      (fun i => hasCompactSupport_scaleTimeLocalizedCutoff hc a δ i)
      (fun i x hx => hγ x (tsupport_scaleTimeLocalizedCutoff_subset χ a δ i hx)) L hβ hf r q

/-- A time piece contributes only at parameters whose actual time center
belongs to its constructed regular compact neighborhood. -/
theorem Family.support_cutoffPartialExtension_time_piece {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (L : FrequencyCutoff) (β : ℝ → ℝ)
    (a δ r : ℝ) (i : ℕ) (f : Plane → ℂ) (K : Set (ℝ × Parameters 2 d))
    (hcenter : ∀ x ∈ tsupport (scaleTimeLocalizedCutoff χ a δ i),
      (a + (i : ℝ) * δ, x.2) ∈ K) :
    Function.support (G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ a δ i) L β r f) ⊆
      {q | (a + (i : ℝ) * δ, q) ∈ K} := by
  intro q hq
  by_contra hn
  have hz : ∀ t, scaleTimeLocalizedCutoff χ a δ i (t, q) = 0 := by
    intro t
    by_contra ht
    exact hn (hcenter (t, q) (subset_closure ht))
  exact hq (by simp only [Family.cutoffPartialExtension, hz, Complex.ofReal_zero,
    zero_mul, integral_zero, smul_zero])

end PlanarNikodym
