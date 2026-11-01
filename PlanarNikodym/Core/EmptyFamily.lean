import PlanarNikodym.Classification.ReuseLocalization

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem Family.noNikodym_of_empty {d : ℕ} (G : Family 2 d) (hW : G.W = ∅) : ¬ G.AdmitsNikodym := by
  rintro ⟨E, F, _, _, _, hpos, hF⟩
  obtain ⟨z, hz⟩ := nonempty_of_measure_ne_zero hpos.ne'
  obtain ⟨u, hu, _⟩ := hF z hz
  simp only [hW, mem_empty_iff_false] at hu

theorem Family.noMassive_of_empty {d : ℕ} (G : Family 2 d) (hW : G.W = ∅) :
    ¬ G.HasMassiveCurveReuse := by
  rintro ⟨β, hβ⟩
  obtain ⟨z, hz⟩ := hβ.nonempty
  obtain ⟨u, hu, _⟩ := (G.mem_centersOf β z).mp hz
  simp only [hW, mem_empty_iff_false] at hu

theorem Family.noLocalUncovered_of_empty {d : ℕ} (G : Family 2 d) (hW : G.W = ∅) :
    ¬ G.LocalReuseNotCovered := by
  intro h
  obtain ⟨z, u, hl, _⟩ := (h Family.Foliations.zero).nonempty
  simpa only [hW, mem_empty_iff_false] using hl.1

theorem Family.classification_of_empty {d : ℕ} (G : Family 2 d) (hW : G.W = ∅) :
    G.AdmitsNikodym ↔ G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered := by
  constructor
  · intro h
    exact (G.noNikodym_of_empty hW h).elim
  · rintro (h | h)
    · exact (G.noMassive_of_empty hW h).elim
    · exact (G.noLocalUncovered_of_empty hW h).elim

end PlanarNikodym
