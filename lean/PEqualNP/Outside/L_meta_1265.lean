import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1265

/-! The blind-gate count is computed by kernel evaluation over the inputs with at most two bits on. -/

end PEqualNP.Outside.L_meta_1265

theorem PEqualNP.Outside.L_meta_1265 :
PEqualNP.BlindGate.blindCount ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 17]⟩], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit) 9 = 0 := by
  set_option synthInstance.maxSize 100000 in
  set_option synthInstance.maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  decide +kernel
