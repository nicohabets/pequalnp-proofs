import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_53475 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808685 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 4]⟩], 20⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
