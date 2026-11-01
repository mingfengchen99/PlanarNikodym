import PlanarNikodym.Analysis.Jets.CutoffGraphJetBounds
import PlanarNikodym.Analysis.Jets.JetInputProductBounds

/-! Quantitative bounds for the actual finite Faa di Bruno amplitudes.
The constants come from compactness of the geometric jets and finite sums. -/
noncomputable section
open Set
open scoped ContDiff

namespace PlanarNikodym

/-- The explicit finite-partition majorant for the actual amplitude.
This algebraic bound needs no differentiability hypothesis on the input. -/
theorem Family.norm_cutoffJetAmplitude_le_partition_sum {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (f : Plane → ℂ) (j : ℕ) (z : Base 2) (t : ℝ) (u : Aux d) :
    ‖G.cutoffJetAmplitude χ f j z t u‖ ≤
      ∑ c : OrderedFinpartition j,
        ‖iteratedFDeriv ℝ c.length (jetInputProduct f) (G.cutoffGraphMap χ z t u)‖ *
          ∏ i : Fin c.length, ‖G.cutoffGraphJet χ (c.partSize i) (t, (z, u))‖ := by
  classical
  unfold Family.cutoffJetAmplitude
  split_ifs with hx
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro c _
    exact c.norm_compAlongOrderedFinpartition_le _ _
  · simp only [norm_zero]
    exact Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

/-- A bound on all geometric jets up to order `j` controls the finite
amplitude by the input product's jets, uniformly in the support point. -/
theorem Family.norm_cutoffJetAmplitude_le_of_graphJet_bound {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (f : Plane → ℂ) (j : ℕ) (z : Base 2) (t : ℝ) (u : Aux d)
    {B : ℝ} (hB : 1 ≤ B)
    (hJ : ∀ m ≤ j, ‖G.cutoffGraphJet χ m (t, (z, u))‖ ≤ B) :
    ‖G.cutoffJetAmplitude χ f j z t u‖ ≤
      (Fintype.card (OrderedFinpartition j) : ℝ) * B ^ j *
        ∑ m ∈ Finset.range (j + 1),
          ‖iteratedFDeriv ℝ m (jetInputProduct f) (G.cutoffGraphMap χ z t u)‖ := by
  classical
  apply (G.norm_cutoffJetAmplitude_le_partition_sum χ f j z t u).trans
  let S : ℝ := ∑ m ∈ Finset.range (j + 1),
    ‖iteratedFDeriv ℝ m (jetInputProduct f) (G.cutoffGraphMap χ z t u)‖
  have hterm (c : OrderedFinpartition j) :
      ‖iteratedFDeriv ℝ c.length (jetInputProduct f) (G.cutoffGraphMap χ z t u)‖ *
          ∏ i : Fin c.length, ‖G.cutoffGraphJet χ (c.partSize i) (t, (z, u))‖ ≤ S * B ^ j := by
    have hinput : ‖iteratedFDeriv ℝ c.length (jetInputProduct f) (G.cutoffGraphMap χ z t u)‖ ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum
        (f := fun m => ‖iteratedFDeriv ℝ m (jetInputProduct f) (G.cutoffGraphMap χ z t u)‖)
        (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le c.length_le))
    have hprod : (∏ i : Fin c.length, ‖G.cutoffGraphJet χ (c.partSize i) (t, (z, u))‖) ≤ B ^ j := by
      calc
        _ ≤ ∏ _i : Fin c.length, B := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun i _ => hJ _ (c.partSize_le i))
        _ = B ^ c.length := by simp
        _ ≤ B ^ j := pow_le_pow_right₀ hB c.length_le
    exact mul_le_mul hinput hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  calc
    _ ≤ ∑ _c : OrderedFinpartition j, S * B ^ j := Finset.sum_le_sum (fun c _ => hterm c)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp [S]; ring

/-- Compact support supplies the geometric constant. It is independent of
the input and of the point; the arbitrary extension outside the support is unused. -/
theorem Family.exists_uniform_cutoffJetAmplitude_product_bound {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Plane → ℂ) (z : Base 2) (t : ℝ) (u : Aux d),
      ‖G.cutoffJetAmplitude χ f j z t u‖ ≤ C *
        ∑ m ∈ Finset.range (j + 1),
          ‖iteratedFDeriv ℝ m (jetInputProduct f) (G.cutoffGraphMap χ z t u)‖ := by
  classical
  obtain ⟨B, hB, hJ⟩ := G.exists_uniform_cutoffGraphJet_bound χ hχ hc hγ j
  let C : ℝ := (Fintype.card (OrderedFinpartition j) : ℝ) * B ^ j + 1
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hcoef : 0 ≤ (Fintype.card (OrderedFinpartition j) : ℝ) * B ^ j := by positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro f z t u
  by_cases hx : (t, (z, u)) ∈ tsupport χ
  · apply (G.norm_cutoffJetAmplitude_le_of_graphJet_bound χ f j z t u hB
      (fun m hm => hJ m hm _ hx)).trans
    gcongr
    dsimp [C]
    linarith
  · simp only [Family.cutoffJetAmplitude, if_neg hx, norm_zero]
    exact mul_nonneg (by dsimp [C]; positivity) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-- Uniform finite-amplitude norm control by the original input's actual
spatial jets. The positive constant is fixed before choosing the input. -/
theorem Family.exists_uniform_cutoffJetAmplitude_bound {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Plane → ℂ), ContDiff ℝ ∞ f →
      ∀ (z : Base 2) (t : ℝ) (u : Aux d),
        ‖G.cutoffJetAmplitude χ f j z t u‖ ≤ C *
          ∑ m ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ m f (G.graphMap (z, u) t)‖ := by
  obtain ⟨A, hA, hAmp⟩ := G.exists_uniform_cutoffJetAmplitude_product_bound χ hχ hc hγ j
  obtain ⟨B, hB, hInput⟩ := exists_sum_norm_iteratedFDeriv_jetInputProduct_bound j
  obtain ⟨x₀, hx₀⟩ := hχ.continuous.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  let M : ℝ := 1 + ‖χ x₀‖
  refine ⟨A * B * M, mul_pos (mul_pos hA hB) (by dsimp [M]; positivity), ?_⟩
  intro f hf z t u
  have hcut : 1 + ‖(χ (t, (z, u)) : ℂ)‖ ≤ M := by
    simpa only [Complex.norm_real, M] using add_le_add (le_refl (1 : ℝ)) (hx₀ (t, (z, u)))
  calc
    _ ≤ A * ∑ m ∈ Finset.range (j + 1),
        ‖iteratedFDeriv ℝ m (jetInputProduct f) (G.cutoffGraphMap χ z t u)‖ := hAmp f z t u
    _ ≤ A * (B * (1 + ‖(χ (t, (z, u)) : ℂ)‖) *
        ∑ m ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ m f (G.graphMap (z, u) t)‖) :=
      mul_le_mul_of_nonneg_left (hInput f hf _ _) hA.le
    _ ≤ A * (B * M * ∑ m ∈ Finset.range (j + 1),
        ‖iteratedFDeriv ℝ m f (G.graphMap (z, u) t)‖) := by gcongr
    _ = _ := by ring

end PlanarNikodym
