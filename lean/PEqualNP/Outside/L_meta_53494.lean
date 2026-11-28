import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_53494 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (815987 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 18]⟩], 20⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
