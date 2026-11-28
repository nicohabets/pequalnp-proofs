import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_53650 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947373 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 19]⟩], 20⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
