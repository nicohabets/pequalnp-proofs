import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1308

/-! Each line-degree is computed gate by gate by kernel evaluation. -/

end PEqualNP.Outside.L_meta_1308

theorem PEqualNP.Outside.L_meta_1308 :
({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 7] }], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit).lineDeg (7 + 7) (Finset.Ico 7 (7 + 7)) = 2 ∧ ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 8] }], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit).lineDeg (7 + 7) (Finset.Ico 7 (7 + 7)) = 2 ∧ ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit).lineDeg (7 + 7) (Finset.Ico 7 (7 + 7)) = 1 ∧ ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 8] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit).lineDeg (7 + 7) (Finset.Ico 7 (7 + 7)) = 2 ∧ ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit).lineDeg (7 + 7) (Finset.Ico 7 (7 + 7)) = 4 ∧ ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 1] }], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit).lineDeg (7 + 7) (Finset.Ico 7 (7 + 7)) = 0 ∧ ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 7] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit).lineDeg (7 + 7) (Finset.Ico 7 (7 + 7)) = 2 ∧ ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 14] }], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit).lineDeg (7 + 7) (Finset.Ico 7 (7 + 7)) = 3 := by
  set_option synthInstance.maxSize 100000 in
  set_option synthInstance.maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  decide +kernel
