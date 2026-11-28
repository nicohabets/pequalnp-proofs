import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_53503 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816681 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 19]⟩], 20⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
