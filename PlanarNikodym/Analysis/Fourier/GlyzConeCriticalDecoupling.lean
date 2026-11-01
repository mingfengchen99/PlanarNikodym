import PlanarNikodym.Analysis.Fourier.GlyzTruncatedConeDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzConeRadialPartition

/-! Critical decoupling for the full truncated cone over an arbitrary
controlled nondegenerate curve. Actual uniformly bounded radial Fourier
projections connect the proved slab estimate to the original pieces. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform NNReal ENNReal BigOperators
namespace PlanarNikodym

theorem glyz_cone_critical_decoupling
    (k : ℕ) (hk : 0 < k) {β B Q ε rmin rmax : ℝ}
    (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) (hrmin : 0 < rmin) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace k,
      ContDiff ℝ (k + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ k + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (f : ℕ → SchwartzMap (GlyzConeSpace k) ℂ),
      (∀ j < 2 ^ N, Function.support (𝓕 (f j : GlyzConeSpace k → ℂ)) ⊆
        glyzConeBox k γ (glyzDyadicCenter N j) (glyzDyadicScale N) Q rmin rmax) →
      lpNorm ((∑ j ∈ Finset.range (2 ^ N), f j : SchwartzMap (GlyzConeSpace k) ℂ) :
        GlyzConeSpace k → ℂ) (glyzCriticalNNExponent k) volume ^ 2 ≤
        C * (2 : ℝ) ^ (ε * N) * ∑ j ∈ Finset.range (2 ^ N),
          lpNorm (f j : GlyzConeSpace k → ℂ) (glyzCriticalNNExponent k) volume ^ 2 := by
  classical
  obtain ⟨σ, C, hσ, _, hC, hslab⟩ :=
    glyz_truncated_cone_critical_decoupling k hk hβ hB hQ hε
  let H := rmax * (B + (k : ℝ) * Q * B)
  obtain ⟨S, χ, M, hM, hχ, hsum, hbound⟩ :=
    exists_glyz_cone_radial_partition k H hrmin hσ
  let A : ℝ := ((Fintype.card S : ℝ) * M) ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  refine ⟨(A + 1) * C, mul_pos (by positivity) hC, fun γ hγ hder hdet N f hf => ?_⟩
  have hfreq (i : ℕ) (hi : i < 2 ^ N) :
      Function.support (𝓕 (f i : GlyzConeSpace k → ℂ)) ⊆
        glyzConeFrequencyRange k H rmin rmax :=
    (hf i hi).trans (glyzConeBox_subset_frequencyRange γ (glyzDyadicScale_pos N).le
      (by simpa only [glyzDyadicScale, pow_zero, inv_one] using
        glyzDyadicScale_antitone (Nat.zero_le N)) hQ.le hB.le hrmin.le
      (fun j hj => hder _ (glyzDyadicCenter_mem_Icc hi) j (by omega)))
  have hdec (a : S) :
      lpNorm ((∑ j ∈ Finset.range (2 ^ N), glyzFourierProjector (χ a) (f j) :
        SchwartzMap (GlyzConeSpace k) ℂ) : GlyzConeSpace k → ℂ)
          (glyzCriticalNNExponent k) volume ^ 2 ≤
        (C * (2 : ℝ) ^ (ε * N)) * ∑ j ∈ Finset.range (2 ^ N),
          lpNorm (glyzFourierProjector (χ a) (f j) : GlyzConeSpace k → ℂ)
            (glyzCriticalNNExponent k) volume ^ 2 := by
    have ha0 : ((a.val : Icc rmin rmax) : ℝ) ≠ 0 :=
      ne_of_gt (hrmin.trans_le a.val.property.1)
    apply hslab γ hγ hder hdet ((a.val : Icc rmin rmax) : ℝ) ha0 N
      (fun j => glyzFourierProjector (χ a) (f j))
    intro j hj z hz
    have hz' := support_fourier_glyzFourierProjector_inter (χ a) (f j) hz
    obtain ⟨r, _, ξ, hξ, rfl⟩ := hf j hj hz'.1
    exact ⟨r, ξ, (hχ a hz'.2).le, hξ, rfl⟩
  have h := glyz_finite_projection_decoupling (Finset.range (2 ^ N)) f
    (fun a : S => glyzFourierProjector (χ a)) (one_le_glyzCriticalNNExponent hk)
    (show 0 ≤ C * (2 : ℝ) ^ (ε * N) by positivity)
    (fun i hi => hsum (f i) (hfreq i (Finset.mem_range.mp hi)))
    (fun a i _ => hbound (glyzCriticalNNExponent k) (one_le_glyzCriticalNNExponent hk) a (f i)) hdec
  apply h.trans
  change A * (C * (2 : ℝ) ^ (ε * N)) * _ ≤ ((A + 1) * C) * (2 : ℝ) ^ (ε * N) * _
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (ε * N)]

end PlanarNikodym
