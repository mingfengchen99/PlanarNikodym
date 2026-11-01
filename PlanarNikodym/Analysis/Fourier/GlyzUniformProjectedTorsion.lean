import PlanarNikodym.Analysis.Fourier.GlyzProjectionFamily

/-! One positive torsion lower bound works for all separated centers.
The matrix and its perturbations are actual Gram matrices of the actual
orthogonally projected derivatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped Matrix.Norms.Elementwise
namespace PlanarNikodym

def glyzProjectedGram (l r : ℕ) (s t : ℝ) : Matrix (Fin l) (Fin l) ℝ :=
  Matrix.gram ℝ (fun j => glyzOrthogonalOperator l r t (glyzEuclideanJetBlock (l + r) l s j))

theorem glyzProjectedGram_eq_derivatives (l r : ℕ) (s t : ℝ) :
    glyzProjectedGram l r s t = Matrix.gram ℝ
      (fun j : Fin l => iteratedDeriv ((j : ℕ) + 1) (glyzOrthogonalCurve l r t) s) := by
  simp_rw [iteratedDeriv_glyzOrthogonalCurve]
  rfl

theorem continuous_glyzProjectedGram (l r : ℕ) :
    Continuous (fun z : ℝ × ℝ => glyzProjectedGram l r z.1 z.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_glyzAmbientProjectedJets l r i).inner (continuous_glyzAmbientProjectedJets l r j)

theorem det_glyzProjectedGram_ne_zero (l r : ℕ) {s t : ℝ} (hst : s ≠ t) :
    (glyzProjectedGram l r s t).det ≠ 0 := by
  rw [glyzProjectedGram_eq_derivatives]
  exact det_gram_glyzOrthogonalCurve_ne_zero l r hst

theorem exists_uniform_glyzProjectedGram_perturbation (l r : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∃ b ε : ℝ, 0 < b ∧ 0 < ε ∧ ∀ z ∈ separatedMixedCenters ν,
      ∀ M : Matrix (Fin l) (Fin l) ℝ,
        dist M (glyzProjectedGram l r z.1 z.2) < ε → b ≤ |M.det| := by
  let K := (fun z : ℝ × ℝ => glyzProjectedGram l r z.1 z.2) '' separatedMixedCenters ν
  have hK : IsCompact K := (isCompact_separatedMixedCenters ν).image
    (continuous_glyzProjectedGram l r)
  have hn : ∀ M ∈ K, 0 < |M.det| := by
    rintro _ ⟨z, hz, rfl⟩
    apply abs_pos.mpr (det_glyzProjectedGram_ne_zero l r ?_)
    intro he
    have : ν ≤ 0 := by simpa [he] using hz.2.2
    exact (not_le_of_gt hν) this
  by_cases he : K.Nonempty
  · obtain ⟨M₀, hM₀, hmin⟩ := hK.exists_isMinOn he continuous_id.matrix_det.abs.continuousOn
    have hb := hn M₀ hM₀
    have ho : IsOpen {M : Matrix (Fin l) (Fin l) ℝ | |M₀.det| / 2 < |M.det|} :=
      isOpen_lt continuous_const continuous_id.matrix_det.abs
    obtain ⟨ε, hε, hstable⟩ := hK.exists_thickening_subset_open ho
      (fun M hM => (half_lt_self hb).trans_le (hmin hM))
    refine ⟨|M₀.det| / 2, ε, half_pos hb, hε, ?_⟩
    intro z hz M hM
    exact (hstable (mem_thickening_iff.mpr
      ⟨glyzProjectedGram l r z.1 z.2, ⟨z, hz, rfl⟩, hM⟩)).le
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro z hz
    exact (he ⟨_, ⟨z, hz, rfl⟩⟩).elim

theorem exists_uniform_glyzOrthogonalCurve_torsion (l r : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∃ b : ℝ, 0 < b ∧ ∀ z ∈ separatedMixedCenters ν,
      b ≤ |(Matrix.gram ℝ (fun j : Fin l =>
        iteratedDeriv ((j : ℕ) + 1) (glyzOrthogonalCurve l r z.2) z.1)).det| := by
  obtain ⟨b, ε, hb, hε, h⟩ := exists_uniform_glyzProjectedGram_perturbation l r hν
  refine ⟨b, hb, fun z hz => ?_⟩
  have h' := h z hz (glyzProjectedGram l r z.1 z.2) (by simpa using hε)
  rwa [glyzProjectedGram_eq_derivatives] at h'

end PlanarNikodym
