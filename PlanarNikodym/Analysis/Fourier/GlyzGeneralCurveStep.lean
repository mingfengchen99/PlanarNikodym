import PlanarNikodym.Analysis.Fourier.GlyzGeneralTaylorNesting
import PlanarNikodym.Analysis.Fourier.GlyzEnlargedMomentDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzDyadicIntervalGeometry

/-! A genuine dyadic refinement estimate for every uniformly controlled
nondegenerate curve. The supports of all intermediate block sums are
proved from the original finest pieces by Taylor nesting. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators NNReal ENNReal FourierTransform
namespace PlanarNikodym

theorem glyzDyadicScale_antitone {n m : ℕ} (hnm : n ≤ m) :
    glyzDyadicScale m ≤ glyzDyadicScale n :=
  (inv_le_inv₀ (by positivity) (by positivity)).mpr
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnm)

theorem glyzDyadicCenter_grandchild_mem_interval {N n m i j v : ℕ}
    (hnm : n ≤ m) (hmN : m ≤ N) (hj : j < 2 ^ (m - n)) (hv : v < 2 ^ (N - m)) :
    glyzDyadicCenter N ((i * 2 ^ (m - n) + j) * 2 ^ (N - m) + v) ∈
      Icc (glyzDyadicLeft n i) (glyzDyadicRight n i) := by
  have h₁ := glyzDyadicCenter_descendant_dist (n := n) (i := i) hj
  have h₂ := glyzDyadicCenter_descendant_dist (n := m) (i := i * 2 ^ (m - n) + j) hv
  rw [Nat.add_sub_of_le hnm] at h₁
  rw [Nat.add_sub_of_le hmN] at h₂
  have ht := abs_sub_le
    (glyzDyadicCenter N ((i * 2 ^ (m - n) + j) * 2 ^ (N - m) + v))
    (glyzDyadicCenter m (i * 2 ^ (m - n) + j)) (glyzDyadicCenter n i)
  have hdist : |glyzDyadicCenter N ((i * 2 ^ (m - n) + j) * 2 ^ (N - m) + v) -
      glyzDyadicCenter n i| ≤ glyzDyadicScale n / 2 := by
    linarith [glyzDyadicScale_pos N]
  have hd := abs_le.mp hdist
  unfold glyzDyadicLeft glyzDyadicRight glyzDyadicCenter at *
  constructor <;> linarith

theorem exists_uniform_glyz_general_curve_step
    (l : ℕ) {β B Q : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q)
    {p : ℝ≥0} (hp : 1 ≤ p) {α : ℝ} (hα : GlyzAdmissibleSquareLoss l p α) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 1 ≤ C ∧ ∀ γ : ℝ → GlyzSpace l,
      ContDiff ℝ (l + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ l + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N n m i : ℕ), n ≤ m → m ≤ N → i < 2 ^ n →
      glyzDyadicScale n < ρ → glyzDyadicScale n ^ (l + 1) ≤ glyzDyadicScale m ^ l →
      ∀ f : ℕ → SchwartzMap (GlyzSpace l) ℂ,
      (∀ j < 2 ^ N, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox γ l (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      lpNorm ((glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace l) ℂ) :
        GlyzSpace l → ℂ) p volume ^ 2 ≤
        (C * (2 : ℝ) ^ (α * (m - n : ℕ))) * glyzDyadicBlock
          (fun j => lpNorm ((glyzDyadicBlock f N m j : SchwartzMap (GlyzSpace l) ℂ) :
            GlyzSpace l → ℂ) p volume ^ 2) m n i := by
  classical
  obtain ⟨ρ, R, hρ, hρ1, hR, hnest⟩ := exists_uniform_glyz_general_curve_taylor_nesting l hβ hB hQ
  obtain ⟨_, _, hinv⟩ := exists_uniform_glyz_general_curve_inverse l hβ hB
  obtain ⟨C, hC, hmoment⟩ := glyz_enlarged_affine_dyadic_decoupling_of_admissible_square_loss hp hα R
  refine ⟨ρ, max C 1, hρ, hρ1, le_max_right _ _, ?_⟩
  intro γ hγ hder hdet N n m i hnm hmN hi hshort hscale f hf
  let a := glyzDyadicLeft n i
  let b := glyzDyadicRight n i
  have hab : a < b := glyzDyadicLeft_lt_right n i
  have hlength : b - a = glyzDyadicScale n := glyzDyadicInterval_length n i
  have ha : a ∈ Icc (0 : ℝ) 1 := glyzDyadicInterval_subset_unit hi ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc (0 : ℝ) 1 := glyzDyadicInterval_subset_unit hi ⟨hab.le, le_rfl⟩
  have he : n + (m - n) = m := Nat.add_sub_of_le hnm
  have he' : m + (N - m) = N := Nat.add_sub_of_le hmN
  obtain ⟨L, hL, _⟩ := hinv γ a (fun j => hder a ha _ (by omega)) (hdet a ha)
  let c : ℕ → ℝ := fun j => glyzDyadicCenter m (i * 2 ^ (m - n) + j)
  let F : ℕ → SchwartzMap (GlyzSpace l) ℂ := fun j => glyzDyadicBlock f N m (i * 2 ^ (m - n) + j)
  have hsupport (j : ℕ) (hj : j ∈ Finset.range (2 ^ (m - n))) :
      ∃ T : GlyzSpace l ≃L[ℝ] GlyzSpace l,
        T.toContinuousLinearMap = glyzCurveJetOperator (glyzTaylorCurve γ l a) (c j) ∧
        Function.support (𝓕 (F j : GlyzSpace l → ℂ)) ⊆
          glyzFrequencyBox (glyzScaledFrame T (glyzDyadicScale m) (glyzDyadicScale_pos m))
            (glyzTaylorCurve γ l a (c j)) R := by
    have hj' := Finset.mem_range.mp hj
    have hc : c j ∈ Icc a b := by
      simpa only [he] using glyzDyadicCenter_descendant_mem_interval (n := n) (i := i) hj'
    obtain ⟨T, hT, hTbox⟩ := hnest γ hγ hder hdet a ha b hb hab
      (by simpa only [hlength] using hshort) (c j) hc (glyzDyadicScale m) (glyzDyadicScale_pos m)
      (by simpa only [hlength] using glyzDyadicScale_antitone hnm)
      (by simpa only [hlength] using hscale)
    refine ⟨T, hT, fun ξ hξ => ?_⟩
    by_contra hout
    have hchild : i * 2 ^ (m - n) + j < 2 ^ m := by
      simpa only [he] using glyz_dyadic_descendant_lt hi hj'
    have hz (v : ℕ) (hv : v < 2 ^ (N - m)) :
        𝓕 (f ((i * 2 ^ (m - n) + j) * 2 ^ (N - m) + v) : GlyzSpace l → ℂ) ξ = 0 := by
      by_contra hvz
      apply hout
      have hidx : (i * 2 ^ (m - n) + j) * 2 ^ (N - m) + v < 2 ^ N := by
        simpa only [he'] using glyz_dyadic_descendant_lt hchild hv
      apply hTbox _ (glyzDyadicCenter_grandchild_mem_interval hnm hmN hj' hv)
        _ (glyzDyadicScale_pos N) (glyzDyadicScale_antitone hmN) ?_ (hf _ hidx hvz)
      have hd := glyzDyadicCenter_descendant_dist (n := m) (i := i * 2 ^ (m - n) + j) hv
      rw [he'] at hd
      dsimp [c]
      linarith [glyzDyadicScale_pos N, glyzDyadicScale_pos m]
    apply hξ
    change (𝓕 (∑ v ∈ Finset.range (2 ^ (N - m)),
      f ((i * 2 ^ (m - n) + j) * 2 ^ (N - m) + v) : SchwartzMap (GlyzSpace l) ℂ)) ξ = 0
    simp only [FourierTransform.fourier_sum, sum_apply]
    exact Finset.sum_eq_zero fun v hv => hz v (Finset.mem_range.mp hv)
  rw [glyzDyadicBlock_refine f N n (m - n) i (by omega), he]
  change lpNorm ((∑ j ∈ Finset.range (2 ^ (m - n)), F j : SchwartzMap (GlyzSpace l) ℂ) :
    GlyzSpace l → ℂ) p volume ^ 2 ≤
    (max C 1 * (2 : ℝ) ^ (α * (m - n : ℕ))) *
      ∑ j ∈ Finset.range (2 ^ (m - n)), lpNorm (F j : GlyzSpace l → ℂ) p volume ^ 2
  apply glyz_taylor_decoupling_transfer γ a (glyzDyadicScale m) R (glyzDyadicScale_pos m)
    L hL _ c F p _ hsupport
  intro g hg
  have hc (j : ℕ) : c j - a = 0 + glyzDyadicScale n * glyzDyadicCenter (m - n) j := by
    have hcenter := glyzDyadicCenter_rescale n (m - n) i j
    rw [he] at hcenter
    dsimp [c, a, glyzDyadicLeft]
    rw [← hcenter]
    ring
  have hδ : glyzDyadicScale m = glyzDyadicScale n * glyzDyadicScale (m - n) := by
    rw [← glyzDyadicScale_add, he]
  have h := hmoment (m - n) 0 (glyzDyadicScale n) (glyzDyadicScale_pos n) g (by
    intro j hj
    simpa only [hc j, hδ] using hg j hj)
  have hcoef : C * (2 : ℝ) ^ (α * (m - n : ℕ)) ≤ max C 1 * (2 : ℝ) ^ (α * (m - n : ℕ)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hfun : ((∑ j ∈ Finset.range (2 ^ (m - n)), g j : SchwartzMap (GlyzSpace l) ℂ) :
      GlyzSpace l → ℂ) = fun x => ∑ j ∈ Finset.range (2 ^ (m - n)), g j x := by
    ext x
    simp only [sum_apply]
  rw [hfun]
  exact h.trans (mul_le_mul_of_nonneg_right hcoef (glyzDyadicSquareEnergy_nonneg l (m - n) p g))

end PlanarNikodym
