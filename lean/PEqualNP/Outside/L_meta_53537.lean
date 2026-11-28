import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_53537 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (838780 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 16]⟩], 20⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
