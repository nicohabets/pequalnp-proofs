import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_400

/-! If a least cover misses `w`, it contains `l` (edge `l w`), and swapping `l` for `w` gives a
cover that is no larger, hence least. Removing `w` from a least cover containing `w` leaves a
cover of the edges avoiding `l` and `w`, one smaller. Conversely, adding `w` to a cover of the
edges avoiding `l` and `w` covers the whole graph, since every edge at `l` goes to `w`. -/

end PEqualNP.Outside.L_meta_400

theorem PEqualNP.Outside.L_meta_400 :
∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (l w : Fin n), G.Adj l w → (∀ v : Fin n, G.Adj l v → v = w) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t ∧ w ∈ S) ∧ (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ≠ l → u ≠ w → v ≠ l → v ≠ w → u ∈ S ∨ v ∈ S) ∧ S.card + 1 = t) ∧ ∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ≠ l → u ≠ w → v ≠ l → v ≠ w → u ∈ S ∨ v ∈ S) → t ≤ S.card + 1 := by
  intro n t G _ l w hl hlw ⟨S0, hS0, hc⟩ hmin
  have hwl : w ≠ l := (G.ne_of_adj hl).symm
  have hA : ∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧
      S.card = t ∧ w ∈ S := by
    by_cases hw : w ∈ S0
    · exact ⟨S0, hS0, hc, hw⟩
    · have hlS : l ∈ S0 := by
        rcases hS0 l w hl with h | h
        · exact h
        · exact absurd h hw
      have hcov : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G (insert w (S0.erase l)) := by
        intro u v h
        by_cases hu : u = l
        · rw [hu] at h; right; simp [hlw v h]
        by_cases hv : v = l
        · rw [hv] at h; left; simp [hlw u h.symm]
        rcases hS0 u v h with h1 | h1
        · left; simp [h1, hu]
        · right; simp [h1, hv]
      have h1 := hmin _ hcov
      have h2 : (insert w (S0.erase l)).card ≤ S0.card :=
        calc _ ≤ (S0.erase l).card + 1 := Finset.card_insert_le _ _
          _ = S0.card := Finset.card_erase_add_one hlS
      exact ⟨_, hcov, by omega, Finset.mem_insert_self _ _⟩
  obtain ⟨S1, hS1, hc1, hw1⟩ := hA
  refine ⟨⟨S1, hS1, hc1, hw1⟩, ⟨S1.erase w, ?_, ?_⟩, ?_⟩
  · intro u v h _ hu _ hv
    rcases hS1 u v h with h1 | h1
    · left; simp [h1, hu]
    · right; simp [h1, hv]
  · rw [Finset.card_erase_add_one hw1, hc1]
  · intro S hS
    have h1 : t ≤ (insert w S).card := by
      apply hmin
      intro u v h
      by_cases hu : u = w
      · left; simp [hu]
      by_cases hv : v = w
      · right; simp [hv]
      by_cases hu' : u = l
      · rw [hu'] at h; exact absurd (hlw v h) hv
      by_cases hv' : v = l
      · rw [hv'] at h; exact absurd (hlw u h.symm) hu
      rcases hS u v h hu' hu hv' hv with h1 | h1
      · left; simp [h1]
      · right; simp [h1]
    have h2 := Finset.card_insert_le w S
    omega
