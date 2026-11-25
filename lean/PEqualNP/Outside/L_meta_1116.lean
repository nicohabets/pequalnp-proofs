import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1116

/-! The gate list is given in the statement; its value is checked on all inputs by kernel evaluation. -/

end PEqualNP.Outside.L_meta_1116

theorem PEqualNP.Outside.L_meta_1116 :
∀ x : Fin 6 → Bool, (⟨[{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }], 14⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = ((fun y : Fin 6 → Bool => (y 0 && y 1) || (y 0 && y 2) || (y 0 && y 3) || (y 0 && y 4) || (y 0 && y 5) || (y 1 && y 2) || (y 1 && y 3) || (y 1 && y 4) || (y 2 && y 3) || (y 2 && y 4)) x) := by
  set_option synthInstance.maxSize 100000 in
  set_option synthInstance.maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  decide +kernel
