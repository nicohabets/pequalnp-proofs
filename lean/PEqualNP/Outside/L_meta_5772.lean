import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_5772 : PEqualNP.MetaComplexity.Monotone2 ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) ∧
  ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit).size = 8 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 4 => (892 : ℕ).testBit (4 * u.val + v.val)) ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    fin_cases hg <;> simp
  · decide
  · decide
