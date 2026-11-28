import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_53695 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275389 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 20]⟩], 21⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
