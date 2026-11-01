import PlanarNikodym.Analysis.Fourier.GlyzConicGeometry
import PlanarNikodym.Analysis.Fourier.GlyzGeneralCurveStep
import PlanarNikodym.Analysis.Fourier.GlyzBandlimitedLocalization

/-! A genuine angular refinement step for radial slabs of a cone over
a controlled curve. The normalized Fourier supports lie in actual
moment cylinders; no cone decoupling estimate is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped FourierTransform NNReal ENNReal BigOperators
namespace PlanarNikodym

/-- A cone box restricted to one relative radial slab. -/
def glyzTruncatedConeBox (k : ℕ) (γ : ℝ → GlyzSpace k) (s δ R a σ : ℝ) : Set (GlyzConeSpace k) :=
  {z | ∃ r : ℝ, ∃ ξ : GlyzSpace k, |r / a - 1| ≤ σ ∧
    ξ ∈ glyzEnlargedCurveBox γ k s δ R ∧ z = WithLp.toLp 2 (r • ξ, r)}

theorem glyzConicEquiv_scaled_cone_point {k : ℕ}
    (P : GlyzSpace k ≃L[ℝ] GlyzSpace k) (v ξ : GlyzSpace k)
    (a : ℝ) (ha : a ≠ 0) (r : ℝ) :
    (glyzConicEquiv ((glyzScalarEquiv a ha).trans P) v).symm
      (WithLp.toLp 2 (r • (v + P ξ), r)) = WithLp.toLp 2 ((r / a) • ξ, r) := by
  apply (glyzConicEquiv ((glyzScalarEquiv a ha).trans P) v).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, glyzConicEquiv_apply]
  simp only [ContinuousLinearEquiv.trans_apply, glyzScalarEquiv_apply,
    map_smul, smul_smul, smul_add]
  have hc : r / a * a = r := div_mul_cancel₀ r ha
  rw [hc, add_comm]

theorem exists_glyz_moment_radial_width_upto (k q : ℕ) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧
      ∀ d ≤ q, ∀ i ∈ Finset.range (2 ^ d), ∀ t : ℝ, |t - 1| ≤ σ → ∀ R : ℝ,
      (fun ξ => t • ξ) ''
        glyzFrequencyBox (glyzMomentFrequencyFrame k (glyzDyadicCenter d i)
          (glyzDyadicScale d) (glyzDyadicScale_pos d))
          ((EuclideanSpace.equiv (Fin k) ℝ).symm (glyzMomentCurve k (glyzDyadicCenter d i))) R ⊆
        glyzFrequencyBox (glyzMomentFrequencyFrame k (glyzDyadicCenter d i)
          (glyzDyadicScale d) (glyzDyadicScale_pos d))
          ((EuclideanSpace.equiv (Fin k) ℝ).symm (glyzMomentCurve k (glyzDyadicCenter d i))) (2 * R + 1) := by
  induction q with
  | zero =>
    obtain ⟨σ, hσ, hσ1, h⟩ := exists_glyz_moment_radial_width k 0
    refine ⟨σ, hσ, hσ1, fun d hd => ?_⟩
    have hd0 : d = 0 := by omega
    subst d
    exact h
  | succ q ih =>
    obtain ⟨σ, hσ, hσ1, h⟩ := ih
    obtain ⟨τ, hτ, _hτ1, h'⟩ := exists_glyz_moment_radial_width k (q + 1)
    refine ⟨min σ τ, lt_min hσ hτ, (min_le_left _ _).trans hσ1, fun d hd i hi t ht R => ?_⟩
    by_cases hdq : d ≤ q
    · exact h d hdq i hi t (ht.trans (min_le_left _ _)) R
    · have he : d = q + 1 := by omega
      subst d
      exact h' i hi t (ht.trans (min_le_right _ _)) R

/-- Dyadic normalization of an actual Taylor box at a child center. -/
theorem glyzTaylorFrequencyBox_dyadic_image {k : ℕ} (γ : ℝ → GlyzSpace k)
    (a κ R : ℝ) (hκ : 0 < κ) (d j : ℕ)
    (L T : GlyzSpace k ≃L[ℝ] GlyzSpace k)
    (hL : L.toContinuousLinearMap = glyzCurveJetOperator γ a)
    (hT : T.toContinuousLinearMap = glyzCurveJetOperator (glyzTaylorCurve γ k a)
      (a + κ * glyzDyadicCenter d j)) :
    glyzFrequencyBox (glyzScaledFrame T (κ * glyzDyadicScale d) (mul_pos hκ (glyzDyadicScale_pos d)))
      (glyzTaylorCurve γ k a (a + κ * glyzDyadicCenter d j)) R =
    (fun ξ => γ a + ((glyzMomentAffineEuclidean k 0 κ hκ.ne').trans
      (glyzTaylorMomentLinear L)) ξ) ''
      glyzFrequencyBox (glyzMomentFrequencyFrame k (glyzDyadicCenter d j)
        (glyzDyadicScale d) (glyzDyadicScale_pos d))
        ((EuclideanSpace.equiv (Fin k) ℝ).symm (glyzMomentCurve k (glyzDyadicCenter d j))) R := by
  rw [glyzTaylorFrequencyBox_affine_image γ a _ _ R _ L T hL hT]
  have hzero : (EuclideanSpace.equiv (Fin k) ℝ).symm (glyzMomentCurve k 0) = 0 := by
    apply (EuclideanSpace.equiv (Fin k) ℝ).injective
    ext u
    simp [glyzMomentCurve]
  have h := glyzMomentFrequencyBox_affine_image_radius k 0 κ
    (glyzDyadicCenter d j) (glyzDyadicScale d) R hκ (glyzDyadicScale_pos d)
  simp only [hzero, zero_add] at h
  rw [add_sub_cancel_left, ← h, ← Set.image_comp]
  rfl


/-- Actual angular decoupling in a fixed radial slab. The small radial
width may depend on the maximal refinement depth; the estimate's
coefficient and the Taylor neighborhood do not. -/
theorem exists_uniform_glyz_cone_dyadic_step
    (k : ℕ) {β B Q : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q)
    {p : ℝ≥0} (hp : 2 ≤ p) {α : ℝ} (hα : GlyzAdmissibleSquareLoss k p α) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 1 ≤ C ∧ ∀ q : ℕ,
      ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ ∀ γ : ℝ → GlyzSpace k,
      ContDiff ℝ (k + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ k + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N n m i : ℕ), n ≤ m → m ≤ N → m - n ≤ q → i < 2 ^ n →
      glyzDyadicScale n < ρ → glyzDyadicScale n ^ (k + 1) ≤ glyzDyadicScale m ^ k →
      ∀ (a : ℝ), a ≠ 0 → ∀ f : ℕ → SchwartzMap (GlyzConeSpace k) ℂ,
      (∀ j < 2 ^ N, Function.support (𝓕 (f j : GlyzConeSpace k → ℂ)) ⊆
        glyzTruncatedConeBox k γ (glyzDyadicCenter N j) (glyzDyadicScale N) Q a σ) →
      lpNorm ((glyzDyadicBlock f N n i : SchwartzMap (GlyzConeSpace k) ℂ) :
        GlyzConeSpace k → ℂ) p volume ^ 2 ≤
        (C * (2 : ℝ) ^ (α * (m - n : ℕ))) * glyzDyadicBlock
          (fun j => lpNorm ((glyzDyadicBlock f N m j : SchwartzMap (GlyzConeSpace k) ℂ) :
            GlyzConeSpace k → ℂ) p volume ^ 2) m n i := by
  classical
  obtain ⟨ρ, R, hρ, hρ1, hR, hnest⟩ := exists_uniform_glyz_general_curve_taylor_nesting k hβ hB hQ
  obtain ⟨_, _, hinv⟩ := exists_uniform_glyz_general_curve_inverse k hβ hB
  obtain ⟨C, hC, hmoment⟩ := glyz_cylindrical_moment_decoupling_of_admissible_loss
    (V := ℝ) hp hα (2 * R + 1)
  refine ⟨ρ, max C 1, hρ, hρ1, le_max_right _ _, fun q => ?_⟩
  obtain ⟨σ, hσ, hσ1, hradial⟩ := exists_glyz_moment_radial_width_upto k q
  refine ⟨σ, hσ, hσ1, ?_⟩
  intro γ hγ hder hdet N n m i hnm hmN hdq hi hshort hscale a ha f hf
  let u := glyzDyadicLeft n i
  let v := glyzDyadicRight n i
  have huv : u < v := glyzDyadicLeft_lt_right n i
  have hlength : v - u = glyzDyadicScale n := glyzDyadicInterval_length n i
  have hu : u ∈ Icc (0 : ℝ) 1 := glyzDyadicInterval_subset_unit hi ⟨le_rfl, huv.le⟩
  have hv : v ∈ Icc (0 : ℝ) 1 := glyzDyadicInterval_subset_unit hi ⟨huv.le, le_rfl⟩
  have he : n + (m - n) = m := Nat.add_sub_of_le hnm
  have he' : m + (N - m) = N := Nat.add_sub_of_le hmN
  obtain ⟨L, hL, _⟩ := hinv γ u (fun j => hder u hu _ (by omega)) (hdet u hu)
  let P := (glyzMomentAffineEuclidean k 0 (glyzDyadicScale n) (glyzDyadicScale_pos n).ne').trans
    (glyzTaylorMomentLinear L)
  let A := glyzConicEquiv ((glyzScalarEquiv a ha).trans P) (γ u)
  let c : ℕ → ℝ := fun j => glyzDyadicCenter m (i * 2 ^ (m - n) + j)
  let F : ℕ → SchwartzMap (GlyzConeSpace k) ℂ := fun j => glyzDyadicBlock f N m (i * 2 ^ (m - n) + j)
  have hcenter (j : ℕ) : c j = u + glyzDyadicScale n * glyzDyadicCenter (m - n) j := by
    have hc := glyzDyadicCenter_rescale n (m - n) i j
    rw [he] at hc
    dsimp [c, u, glyzDyadicLeft]
    rw [← hc]
  have hδ : glyzDyadicScale m = glyzDyadicScale n * glyzDyadicScale (m - n) := by
    rw [← glyzDyadicScale_add, he]
  have hsupport (j : ℕ) (hj : j ∈ Finset.range (2 ^ (m - n))) :
      Function.support (𝓕 (glyzSchwartzFrequencyAffine A.symm 0 (F j) : GlyzConeSpace k → ℂ)) ⊆
        {z | (WithLp.ofLp z).1 ∈ glyzFrequencyBox
          (glyzMomentFrequencyFrame k (glyzDyadicCenter (m - n) j)
            (glyzDyadicScale (m - n)) (glyzDyadicScale_pos (m - n)))
          ((EuclideanSpace.equiv (Fin k) ℝ).symm (glyzMomentCurve k (glyzDyadicCenter (m - n) j)))
          (2 * R + 1)} := by
    have hj' := Finset.mem_range.mp hj
    have hc : c j ∈ Icc u v := by
      simpa only [he] using glyzDyadicCenter_descendant_mem_interval (n := n) (i := i) hj'
    obtain ⟨T, hT, hTbox⟩ := hnest γ hγ hder hdet u hu v hv huv
      (by simpa only [hlength] using hshort) (c j) hc (glyzDyadicScale m) (glyzDyadicScale_pos m)
      (by simpa only [hlength] using glyzDyadicScale_antitone hnm)
      (by simpa only [hlength] using hscale)
    have hbox : glyzFrequencyBox (glyzScaledFrame T (glyzDyadicScale m) (glyzDyadicScale_pos m))
        (glyzTaylorCurve γ k u (c j)) R =
        (fun ξ => γ u + P ξ) '' glyzFrequencyBox
          (glyzMomentFrequencyFrame k (glyzDyadicCenter (m - n) j)
            (glyzDyadicScale (m - n)) (glyzDyadicScale_pos (m - n)))
          ((EuclideanSpace.equiv (Fin k) ℝ).symm (glyzMomentCurve k (glyzDyadicCenter (m - n) j))) R := by
      simpa only [← hδ, ← hcenter j] using
        glyzTaylorFrequencyBox_dyadic_image γ u (glyzDyadicScale n) R
          (glyzDyadicScale_pos n) (m - n) j L T hL (by simpa only [hcenter j] using hT)
    intro z hz
    rw [support_fourier_glyzSchwartzFrequencyAffine] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simp only [zero_add]
    by_contra hout
    have hchild : i * 2 ^ (m - n) + j < 2 ^ m := by
      simpa only [he] using glyz_dyadic_descendant_lt hi hj'
    have hzleaf (b : ℕ) (hb : b < 2 ^ (N - m)) :
        𝓕 (f ((i * 2 ^ (m - n) + j) * 2 ^ (N - m) + b) : GlyzConeSpace k → ℂ) w = 0 := by
      by_contra hne
      have hidx : (i * 2 ^ (m - n) + j) * 2 ^ (N - m) + b < 2 ^ N := by
        simpa only [he'] using glyz_dyadic_descendant_lt hchild hb
      obtain ⟨r, ξ, hr, hξ, hw'⟩ := hf _ hidx hne
      have hξ' := hTbox _ (glyzDyadicCenter_grandchild_mem_interval hnm hmN hj' hb)
        _ (glyzDyadicScale_pos N) (glyzDyadicScale_antitone hmN) (by
          have hd := glyzDyadicCenter_descendant_dist (n := m) (i := i * 2 ^ (m - n) + j) hb
          rw [he'] at hd
          dsimp [c]
          linarith [glyzDyadicScale_pos N, glyzDyadicScale_pos m]) hξ
      rw [hbox] at hξ'
      obtain ⟨ζ, hζ, hζeq⟩ := hξ'
      apply hout
      rw [hw', ← hζeq]
      dsimp only [A]
      rw [glyzConicEquiv_scaled_cone_point P (γ u) ζ a ha r]
      exact hradial (m - n) hdq j hj (r / a) hr R ⟨ζ, hζ, rfl⟩
    apply hw
    change (𝓕 (∑ b ∈ Finset.range (2 ^ (N - m)),
      f ((i * 2 ^ (m - n) + j) * 2 ^ (N - m) + b) : SchwartzMap (GlyzConeSpace k) ℂ)) w = 0
    simp only [FourierTransform.fourier_sum, sum_apply]
    exact Finset.sum_eq_zero fun b hb => hzleaf b (Finset.mem_range.mp hb)
  rw [glyzDyadicBlock_refine f N n (m - n) i (by omega), he]
  change lpNorm ((∑ j ∈ Finset.range (2 ^ (m - n)), F j : SchwartzMap (GlyzConeSpace k) ℂ) :
    GlyzConeSpace k → ℂ) p volume ^ 2 ≤
    (max C 1 * (2 : ℝ) ^ (α * (m - n : ℕ))) *
      ∑ j ∈ Finset.range (2 ^ (m - n)), lpNorm (F j : GlyzConeSpace k → ℂ) p volume ^ 2
  apply glyz_affine_decoupling_transfer A.symm 0 _ F p
  exact (hmoment (m - n) _ hsupport).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity))
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

end PlanarNikodym
