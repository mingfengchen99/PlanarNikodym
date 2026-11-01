import PlanarNikodym.Classification.ReuseLocalization

/-! Countable unions of foliations with an arbitrary, possibly empty,
countable index type. Missing codes contribute the zero fields. -/

noncomputable section
namespace PlanarNikodym

def Family.Foliations.countableUnion {ι : Type*} [Countable ι]
    (V : ι → Family.Foliations) : Family.Foliations := by
  classical
  letI := Encodable.ofCountable ι
  exact Family.Foliations.iUnion
    (fun n => (Encodable.decode (α := ι) n).elim Family.Foliations.zero V)

theorem Family.covered_countableUnion {d : ℕ} (G : Family 2 d)
    {ι : Type*} [Countable ι] (V : ι → Family.Foliations) (i : ι)
    (p : Parameters 2 d) (h : G.Covered (V i) p) :
    G.Covered (Family.Foliations.countableUnion V) p := by
  classical
  letI := Encodable.ofCountable ι
  apply G.covered_iUnion _ (Encodable.encode i) p
  simpa using h

end PlanarNikodym
