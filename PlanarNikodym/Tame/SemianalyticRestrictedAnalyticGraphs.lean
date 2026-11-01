import PlanarNikodym.Geometry.SemianalyticBasicSets

/-! The actual graph of every restricted analytic function is globally
semianalytic, including jumps on the closed cube boundary and the arbitrary
ambient extension of the function outside its analytic neighborhood. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace PlanarNikodym

theorem locallySemianalytic_restrictedAnalyticFunction_graph {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : AnalyticOnNhd ℝ f (restrictedAnalyticCube n)) :
    LocallySemianalytic {w : Fin (n + 1) → ℝ |
      restrictedAnalyticFunction f (Fin.tail w) = w 0} := by
  classical
  have hcube : LocallySemianalytic {w : Fin (n + 1) → ℝ |
      Fin.tail w ∈ restrictedAnalyticCube n} :=
    (locallySemianalytic_restrictedAnalyticCube n).preimage_analytic Fin.tail analyticAt_finTail
  have htail : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) :=
    continuous_iff_continuousAt.mpr (fun w => (analyticAt_finTail w).continuousAt)
  intro w
  by_cases hw : Fin.tail w ∈ restrictedAnalyticCube n
  · obtain ⟨O, hO, hwO, J, hJ, c, hc, Q, hrep⟩ := hcube w
    let g : J ⊕ Fin 2 → (Fin (n + 1) → ℝ) → ℝ :=
      Sum.elim c (fun i y => if i = 0 then f (Fin.tail y) - y 0 else y 0)
    have hg (j : J ⊕ Fin 2) : AnalyticAt ℝ (g j) w := by
      rcases j with j | i
      · exact hc j w hwO
      · by_cases hi : i = 0
        · simp only [g, Sum.elim_inr, if_pos hi]
          exact ((hf (Fin.tail w) hw).comp (analyticAt_finTail w)).sub (analyticAt_coordinate 0 w)
        · simp only [g, Sum.elim_inr, if_neg hi]
          exact analyticAt_coordinate 0 w
    have hnear : {y | y ∈ O ∧ ∀ j, AnalyticAt ℝ (g j) y} ∈ 𝓝 w :=
      inter_mem (hO.mem_nhds hwO) (Filter.eventually_all.mpr (fun j => (hg j).eventually_analyticAt))
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hnear
    refine ⟨ball w r, isOpen_ball, mem_ball_self hr, J ⊕ Fin 2, inferInstance, g,
      (fun j y hy => (hsub hy).2 j),
      (fun s => if Q (fun j => s (Sum.inl j)) then s (Sum.inr 0) = 1 else s (Sum.inr 1) = 1), ?_⟩
    intro y hy
    have he := hrep y (hsub hy).1
    change restrictedAnalyticFunction f (Fin.tail y) = y 0 ↔
      (if Q (fun j => oneDimensionalSign (c j y))
        then oneDimensionalSign (f (Fin.tail y) - y 0) = 1 else oneDimensionalSign (y 0) = 1)
    by_cases hyc : Fin.tail y ∈ restrictedAnalyticCube n
    · have hQ := he.mp hyc
      simp only [restrictedAnalyticFunction, if_pos hyc, if_pos hQ,
        oneDimensionalSign_eq_one, sub_eq_zero]
    · have hQ := mt he.mpr hyc
      simp only [restrictedAnalyticFunction, if_neg hyc, if_neg hQ, oneDimensionalSign_eq_one]
      exact eq_comm
  · let O : Set (Fin (n + 1) → ℝ) := {y | Fin.tail y ∉ restrictedAnalyticCube n}
    have hO : IsOpen O :=
      (isClosed_Icc.preimage htail).isOpen_compl
    refine ⟨O, hO, hw, Fin 1, inferInstance, (fun _ y => y 0),
      (fun _ y _ => analyticAt_coordinate 0 y), (fun s => s 0 = 1), ?_⟩
    intro y hy
    change Fin.tail y ∉ restrictedAnalyticCube n at hy
    change restrictedAnalyticFunction f (Fin.tail y) = y 0 ↔ oneDimensionalSign (y 0) = 1
    simp only [restrictedAnalyticFunction, if_neg hy, oneDimensionalSign_eq_one]
    exact eq_comm

end PlanarNikodym
