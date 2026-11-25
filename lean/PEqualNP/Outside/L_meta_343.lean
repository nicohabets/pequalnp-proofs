import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_343

/-! An edge with both ends on is owned by some listed owner with the other end among its owned
neighbours, so that owner term is on; conversely an on owner term exhibits an edge, since every
owned neighbour is adjacent to its owner. -/

end PEqualNP.Outside.L_meta_343

theorem PEqualNP.Outside.L_meta_343 :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) (os : List (Fin n × List (Fin n))), (∀ o ∈ os, ∀ b ∈ o.2, G.Adj o.1 b) → (∀ i j : Fin n, G.Adj i j → ∃ o ∈ os, (o.1 = i ∧ j ∈ o.2) ∨ (o.1 = j ∧ i ∈ o.2)) → ∀ x : Fin n → Bool, (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) ↔ os.any (fun o => x o.1 && o.2.any x) = true := by
  intro n G os h1 h2 x
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    obtain ⟨o, ho, h⟩ := h2 i j hij
    simp only [List.any_eq_true, Bool.and_eq_true]
    rcases h with ⟨e, hm⟩ | ⟨e, hm⟩
    · exact ⟨o, ho, by rw [e]; exact hi, j, hm, hj⟩
    · exact ⟨o, ho, by rw [e]; exact hj, i, hm, hi⟩
  · intro h
    simp only [List.any_eq_true, Bool.and_eq_true] at h
    obtain ⟨o, ho, hx, b, hb, hxb⟩ := h
    exact ⟨o.1, b, h1 o ho b hb, hx, hxb⟩
