import PlanarNikodym.Analysis.Fourier.GlyzTaylorJets

/-! Actual Fourier-box points for curves, and a uniform quantitative
comparison between the projected curve boxes and their Taylor boxes. -/
noncomputable section
open Set
open scoped BigOperators
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def glyzCurveBoxPoint (γ : ℝ → E) (l : ℕ) (s δ : ℝ) (v : Base l) : E :=
  γ s + ∑ j : Fin l, (δ ^ ((j : ℕ) + 1) * v j) • iteratedDeriv ((j : ℕ) + 1) γ s

def glyzCurveBox (γ : ℝ → E) (l : ℕ) (s δ : ℝ) : Set E :=
  glyzCurveBoxPoint γ l s δ '' {v : Base l | ∀ j, |v j| ≤ 1}

theorem norm_glyzCurveBoxPoint_sub_le (γ P : ℝ → E) (l : ℕ) (s δ : ℝ) (v : Base l) :
    ‖glyzCurveBoxPoint γ l s δ v - glyzCurveBoxPoint P l s δ v‖ ≤
      ‖γ s - P s‖ + ∑ j : Fin l, |δ ^ ((j : ℕ) + 1) * v j| *
        ‖iteratedDeriv ((j : ℕ) + 1) γ s - iteratedDeriv ((j : ℕ) + 1) P s‖ := by
  have he : glyzCurveBoxPoint γ l s δ v - glyzCurveBoxPoint P l s δ v =
      (γ s - P s) + ∑ j : Fin l, (δ ^ ((j : ℕ) + 1) * v j) •
        (iteratedDeriv ((j : ℕ) + 1) γ s - iteratedDeriv ((j : ℕ) + 1) P s) := by
    simp only [glyzCurveBoxPoint, smul_sub, Finset.sum_sub_distrib]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add_right
  exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun j _ => by rw [norm_smul, Real.norm_eq_abs])

theorem exists_uniform_glyzCurveBoxPoint_taylor_bound (l r : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ t a b : ℝ,
      a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 → a < b →
      ∀ s ∈ Icc a b, ∀ δ : ℝ, 0 < δ → δ ≤ b - a →
      ∀ v : Base l, (∀ j, |v j| ≤ 1) →
        ‖glyzCurveBoxPoint (glyzCoordinateCurve l r t) l s δ v -
          glyzCurveBoxPoint (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) l s δ v‖ ≤
            K * (b - a) ^ (l + 1) := by
  obtain ⟨C, hC, hT⟩ := exists_uniform_glyzCoordinateCurve_taylor_bound l r
  refine ⟨((l : ℝ) + 1) * C, by positivity, ?_⟩
  intro t a b ha hb hab s hs δ hδ hδb v hv
  have hκ : 0 < b - a := sub_pos.mpr hab
  have hsa : 0 ≤ s - a := sub_nonneg.mpr hs.1
  have hsκ : s - a ≤ b - a := sub_le_sub_right hs.2 a
  have herr (j : ℕ) (hj : j ≤ l) :
      ‖iteratedDeriv j (glyzCoordinateCurve l r t) s -
        iteratedDeriv j (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) s‖ ≤
          C * (b - a) ^ (l - j + 1) := by
    calc
      _ ≤ C * (s - a) ^ (l - j + 1) / (l - j).factorial := hT t a b ha hb hab s hs j hj
      _ ≤ C * (s - a) ^ (l - j + 1) := div_le_self
        (mul_nonneg hC.le (pow_nonneg hsa _)) (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (l - j)))
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsa hsκ _) hC.le
  have hzero : ‖glyzCoordinateCurve l r t s -
      glyzTaylorCurve (glyzCoordinateCurve l r t) l a s‖ ≤ C * (b - a) ^ (l + 1) := by
    simpa only [iteratedDeriv_zero, Nat.sub_zero] using herr 0 (Nat.zero_le l)
  have hterm (j : Fin l) : |δ ^ ((j : ℕ) + 1) * v j| *
      ‖iteratedDeriv ((j : ℕ) + 1) (glyzCoordinateCurve l r t) s -
        iteratedDeriv ((j : ℕ) + 1) (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) s‖ ≤
          C * (b - a) ^ (l + 1) := by
    have hj : (j : ℕ) + 1 ≤ l := j.isLt
    have hcoeff : |δ ^ ((j : ℕ) + 1) * v j| ≤ (b - a) ^ ((j : ℕ) + 1) := by
      rw [abs_mul, abs_of_pos (pow_pos hδ _)]
      exact (mul_le_of_le_one_right (pow_nonneg hδ.le _) (hv j)).trans
        (pow_le_pow_left₀ hδ.le hδb _)
    calc
      _ ≤ (b - a) ^ ((j : ℕ) + 1) * (C * (b - a) ^ (l - ((j : ℕ) + 1) + 1)) :=
        mul_le_mul hcoeff (herr _ hj) (norm_nonneg _) (pow_nonneg hκ.le _)
      _ = _ := by
        rw [mul_left_comm _ C, ← pow_add,
          show (j : ℕ) + 1 + (l - ((j : ℕ) + 1) + 1) = l + 1 by omega]
  have h := (norm_glyzCurveBoxPoint_sub_le (glyzCoordinateCurve l r t)
    (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) l s δ v).trans
      (add_le_add hzero (Finset.sum_le_sum fun j _ => hterm j))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    add_mul, one_mul, add_comm, mul_assoc] using h

theorem exists_uniform_glyzCurveBox_taylor_distance (l r : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ t a b : ℝ,
      a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 → a < b →
      ∀ s ∈ Icc a b, ∀ δ : ℝ, 0 < δ → δ ≤ b - a →
      ∀ ξ ∈ glyzCurveBox (glyzCoordinateCurve l r t) l s δ,
        ∃ η ∈ glyzCurveBox (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) l s δ,
          ‖ξ - η‖ ≤ K * (b - a) ^ (l + 1) := by
  obtain ⟨K, hK, h⟩ := exists_uniform_glyzCurveBoxPoint_taylor_bound l r
  refine ⟨K, hK, ?_⟩
  intro t a b ha hb hab s hs δ hδ hδb ξ hξ
  obtain ⟨v, hv, rfl⟩ := hξ
  exact ⟨_, ⟨v, hv, rfl⟩, h t a b ha hb hab s hs δ hδ hδb v hv⟩

end PlanarNikodym
