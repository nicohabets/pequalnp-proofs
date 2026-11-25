import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1285

/-! Appending a gate appends its degree to the wire list, and the degree list does not depend on the output. The new gate is wire n + |gs|, and an OR gate has the maximum of the degrees of the wires it reads. -/

open PEqualNP.CircuitLowerBounds

theorem ld_snoc (gs : List Gate) (g : Gate) (o o' n : ℕ) (marked : Finset ℕ) :
    Circuit.lineDegrees ⟨gs ++ [g], o⟩ n marked =
      Circuit.lineDegrees ⟨gs, o'⟩ n marked ++
        [g.lineDegree (Circuit.lineDegrees ⟨gs, o'⟩ n marked)] := by
  simp [Circuit.lineDegrees, List.foldl_append]

theorem ld_length (gs : List Gate) (o n : ℕ) (marked : Finset ℕ) :
    (Circuit.lineDegrees ⟨gs, o⟩ n marked).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.lineDegrees]
  | append_singleton gs g ih => rw [ld_snoc _ _ _ o]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [this]

end PEqualNP.Outside.L_meta_1285

theorem PEqualNP.Outside.L_meta_1285 :
∀ (n : ℕ) (marked : Finset ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), a < n + gs.length → b < n + gs.length → ({ gates := gs ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩], output := n + gs.length } : PEqualNP.CircuitLowerBounds.Circuit).lineDeg n marked = max (({ gates := gs, output := a } : PEqualNP.CircuitLowerBounds.Circuit).lineDeg n marked) (({ gates := gs, output := b } : PEqualNP.CircuitLowerBounds.Circuit).lineDeg n marked) := by
  open PEqualNP.Outside.L_meta_1285 PEqualNP.CircuitLowerBounds in
  intro n marked gs a b ha hb
  rw [Circuit.lineDeg, Circuit.lineDeg, Circuit.lineDeg]
  dsimp only
  rw [ld_snoc _ _ _ 0, getD_snoc, ld_length, if_neg (by omega), if_pos rfl]
  have e1 : ∀ o : ℕ, Circuit.lineDegrees ⟨gs, o⟩ n marked = Circuit.lineDegrees ⟨gs, 0⟩ n marked :=
    fun o => rfl
  simp only [e1]
  simp [Gate.lineDegree]
