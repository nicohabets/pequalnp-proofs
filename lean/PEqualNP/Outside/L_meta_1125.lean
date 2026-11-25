import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1125

/-! The gate list is given in the statement; its value is checked on all inputs by kernel evaluation. -/

end PEqualNP.Outside.L_meta_1125

theorem PEqualNP.Outside.L_meta_1125 :
∀ x : Fin 6 → Bool, (⟨[{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 13] }], 14⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = ((fun y : Fin 6 → Bool => (y 0 && y 1) || (y 0 && y 2) || (y 0 && y 3) || (y 0 && y 4) || (y 0 && y 5) || (y 1 && y 2) || (y 1 && y 3) || (y 1 && y 4) || (y 1 && y 5) || (y 2 && y 3) || (y 2 && y 4) || (y 2 && y 5)) x) := by
  set_option synthInstance.maxSize 100000 in
  set_option synthInstance.maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  decide +kernel
