import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53771 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100922 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
