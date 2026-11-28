import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_53593 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (907119 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 16]⟩], 20⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
