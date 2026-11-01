import PlanarNikodym.Analysis.Fourier.GlyzFrequencyBoxes
import PlanarNikodym.Analysis.Fourier.GlyzMomentJets
import PlanarNikodym.Analysis.Fourier.CoefficientDilation

/-! The actual derivative frames, Fourier boxes and polar weights of
Gamma(t)=(t,...,t^m), at arbitrary centers and positive scales. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform NNReal ENNReal
namespace PlanarNikodym

def glyzMomentFrame (m : ℕ) (c : ℝ) : Base m ≃L[ℝ] Base m :=
  (Matrix.toLin' (glyzMixedMomentMatrix m 0 c (c + 1))).equivOfDetNeZero
    (by rw [LinearMap.det_toLin']; exact det_glyzMixedMomentMatrix_ne_zero m 0 (by linarith))
    |>.toContinuousLinearEquiv

theorem glyzMomentFrame_apply (m : ℕ) (c : ℝ) (v : Base m) :
    glyzMomentFrame m c v = (glyzMixedMomentMatrix m 0 c (c + 1)).mulVec v := by
  rfl

theorem glyzMomentFrame_single (m : ℕ) (c : ℝ) (j : Fin m) :
    glyzMomentFrame m c (Pi.single j 1) = glyzMomentJetBlock m m c j := by
  rw [glyzMomentFrame_apply, Matrix.mulVec_single_one]
  ext k
  exact glyzMixedMomentMatrix_apply_left m 0 c (c + 1) j k

def glyzMomentFrequencyFrame (m : ℕ) (c δ : ℝ) (hδ : 0 < δ) :
    GlyzSpace m ≃L[ℝ] GlyzSpace m :=
  (EuclideanSpace.equiv (Fin m) ℝ).trans
    ((coefficientDilation (fun j : Fin m => δ ^ ((j : ℕ) + 1))
      (fun _ => pow_ne_zero _ hδ.ne')).trans (glyzMomentFrame m c)) |>.trans
        (EuclideanSpace.equiv (Fin m) ℝ).symm

theorem glyzMomentFrequencyFrame_basis (m : ℕ) (c δ : ℝ) (hδ : 0 < δ) (j : Fin m) :
    glyzMomentFrequencyFrame m c δ hδ (EuclideanSpace.basisFun (Fin m) ℝ j) =
      δ ^ ((j : ℕ) + 1) • (EuclideanSpace.equiv (Fin m) ℝ).symm
        (glyzMomentJetBlock m m c j) := by
  have he : (EuclideanSpace.equiv (Fin m) ℝ) (EuclideanSpace.basisFun (Fin m) ℝ j) =
      Pi.single j 1 := by ext k; simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
  have hd : coefficientDilation (fun j : Fin m => δ ^ ((j : ℕ) + 1))
      (fun _ => pow_ne_zero _ hδ.ne') (Pi.single j 1) =
      δ ^ ((j : ℕ) + 1) • (Pi.single j 1 : Base m) := by
    ext k
    by_cases hk : k = j <;> simp [hk, Pi.smul_apply]
  simp only [glyzMomentFrequencyFrame, ContinuousLinearEquiv.trans_apply, he, hd,
    map_smul, glyzMomentFrame_single]

def glyzMomentFrequencyBox (m : ℕ) (c δ : ℝ) (hδ : 0 < δ) : Set (GlyzSpace m) :=
  glyzFrequencyBox (glyzMomentFrequencyFrame m c δ hδ)
    ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m c)) 1

theorem glyzMomentPolarBox_mem (m : ℕ) (c δ : ℝ) (hδ : 0 < δ) (x : GlyzSpace m) :
    x ∈ glyzPolarBox (glyzMomentFrequencyFrame m c δ hδ) ↔
      ∀ j : Fin m, |inner ℝ x ((EuclideanSpace.equiv (Fin m) ℝ).symm
        (glyzMomentJetBlock m m c j))| ≤ (δ ^ ((j : ℕ) + 1))⁻¹ := by
  simp only [glyzPolarBox, mem_setOf_eq, glyzMomentFrequencyFrame_basis,
    inner_smul_right, abs_mul, abs_of_pos (pow_pos hδ _)]
  apply forall_congr'
  intro j
  rw [mul_comm, ← le_div_iff₀ (pow_pos hδ _), one_div]

/-- Lemma 3.3 for the actual moment-curve boxes. One constant works for
every center, every positive scale, every supported Schwartz piece and
every physical point. -/
theorem glyz_moment_uncertainty (m A : ℕ) {p : ℝ≥0} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c δ : ℝ) (hδ : 0 < δ)
      (f : SchwartzMap (GlyzSpace m) ℂ),
      Function.support (𝓕 (f : GlyzSpace m → ℂ)) ⊆ glyzMomentFrequencyBox m c δ hδ →
      ∀ x, ‖f x‖ₑ ^ (p : ℝ) ≤ ENNReal.ofReal C *
        ∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) * ENNReal.ofReal
          (glyzPolarWeight A (glyzMomentFrequencyFrame m c δ hδ) y) := by
  obtain ⟨C, hC, h⟩ := glyz_uncertainty_fourier_box m A 1 zero_lt_one hp
  exact ⟨C, hC, fun c δ hδ f hs x => h _ _ f hs x⟩

end PlanarNikodym
