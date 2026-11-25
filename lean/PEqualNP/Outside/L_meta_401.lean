import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_401

/-! A least cover of the graph covers the edges avoiding `l`, so the cover number does not grow.
Conversely, let `S` cover the edges avoiding `l`. If `w` is in `S`, then `S` also covers the
edge `l w`, the only edge at `l`. Otherwise the edge `l' w` forces `l'` into `S`, and swapping
`l'` for `w` gives a cover of the whole graph that is no larger. -/

end PEqualNP.Outside.L_meta_401

theorem PEqualNP.Outside.L_meta_401 :
∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (l l' w : Fin n), l ≠ l' → G.Adj l w → G.Adj l' w → (∀ v : Fin n, G.Adj l v → v = w) → (∀ v : Fin n, G.Adj l' v → v = w) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ≠ l → v ≠ l → u ∈ S ∨ v ∈ S) ∧ S.card = t) ∧ ∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ≠ l → v ≠ l → u ∈ S ∨ v ∈ S) → t ≤ S.card := by
  intro n t G _ l l' w hll' hl hl' hlw hl'w ⟨S0, hS0, hc⟩ hmin
  refine ⟨⟨S0, fun u v h _ _ => hS0 u v h, hc⟩, ?_⟩
  intro S hS
  have hwl : w ≠ l := (G.ne_of_adj hl).symm
  by_cases hw : w ∈ S
  · apply hmin
    intro u v h
    by_cases hu : u = l
    · rw [hu] at h; right; rw [hlw v h]; exact hw
    by_cases hv : v = l
    · rw [hv] at h; left; rw [hlw u h.symm]; exact hw
    exact hS u v h hu hv
  · have hl'S : l' ∈ S := by
      rcases hS l' w hl' (Ne.symm hll') hwl with h | h
      · exact h
      · exact absurd h hw
    have h1 : t ≤ (insert w (S.erase l')).card := by
      apply hmin
      intro u v h
      by_cases hu : u = l
      · rw [hu] at h; right; simp [hlw v h]
      by_cases hv : v = l
      · rw [hv] at h; left; simp [hlw u h.symm]
      rcases hS u v h hu hv with h1 | h1
      · by_cases hu' : u = l'
        · rw [hu'] at h; right; simp [hl'w v h]
        · left; simp [h1, hu']
      · by_cases hv' : v = l'
        · rw [hv'] at h; left; simp [hl'w u h.symm]
        · right; simp [h1, hv']
    have h2 : (insert w (S.erase l')).card ≤ S.card :=
      calc _ ≤ (S.erase l').card + 1 := Finset.card_insert_le _ _
        _ = S.card := Finset.card_erase_add_one hl'S
    omega
