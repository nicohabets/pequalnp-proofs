import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1109

/-! The gate list is given in the statement; its value is checked on all inputs by kernel evaluation. -/

end PEqualNP.Outside.L_meta_1109

theorem PEqualNP.Outside.L_meta_1109 :
∀ x : Fin 5 → Bool, (⟨[{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }], 12⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = ((fun y : Fin 5 → Bool => (y 0 && y 1) || (y 0 && y 2) || (y 0 && y 3) || (y 0 && y 4) || (y 1 && y 2) || (y 1 && y 3) || (y 1 && y 4) || (y 2 && y 3) || (y 2 && y 4)) x) := by
  set_option synthInstance.maxSize 100000 in
  set_option synthInstance.maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  decide +kernel
