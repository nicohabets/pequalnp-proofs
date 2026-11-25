import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1309

/-! Appending a gate appends its degree to the wire list (the fold over gates is taken one gate further); an OR gate of a and b has degree max (deg a) (deg b), and the output n + |gs| is the new last wire. -/

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

end PEqualNP.Outside.L_meta_1309

theorem PEqualNP.Outside.L_meta_1309 :
∀ (n : ℕ) (marked : Finset ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), (PEqualNP.CircuitLowerBounds.Circuit.lineDegrees { gates := gs ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [a, b]], output := 0 } n marked = PEqualNP.CircuitLowerBounds.Circuit.lineDegrees { gates := gs, output := 0 } n marked ++ [max ((PEqualNP.CircuitLowerBounds.Circuit.lineDegrees { gates := gs, output := 0 } n marked).getD a 0) ((PEqualNP.CircuitLowerBounds.Circuit.lineDegrees { gates := gs, output := 0 } n marked).getD b 0)]) ∧ (PEqualNP.CircuitLowerBounds.Circuit.lineDeg { gates := gs ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [a, b]], output := n + gs.length } n marked = max ((PEqualNP.CircuitLowerBounds.Circuit.lineDegrees { gates := gs, output := 0 } n marked).getD a 0) ((PEqualNP.CircuitLowerBounds.Circuit.lineDegrees { gates := gs, output := 0 } n marked).getD b 0)) := by
  open PEqualNP.Outside.L_meta_1309 PEqualNP.CircuitLowerBounds in
  intro n marked gs a b
  have hg : (Gate.mk GateOp.or [a, b]).lineDegree (Circuit.lineDegrees ⟨gs, 0⟩ n marked) =
      max ((Circuit.lineDegrees ⟨gs, 0⟩ n marked).getD a 0)
        ((Circuit.lineDegrees ⟨gs, 0⟩ n marked).getD b 0) := by
    simp [Gate.lineDegree]
  refine ⟨?_, ?_⟩
  · rw [ld_snoc _ _ _ 0, hg]
  · rw [Circuit.lineDeg]
    dsimp only
    rw [ld_snoc _ _ _ 0, getD_snoc, ld_length, if_neg (by omega), if_pos rfl, hg]
