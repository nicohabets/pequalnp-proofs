import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_5595 : PEqualNP.MetaComplexity.Monotone2 ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 1] }], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit) ∧
  ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 1] }], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit).size = 5 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 4 => (32767 : ℕ).testBit (4 * u.val + v.val)) ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 1] }], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    fin_cases hg <;> simp
  · decide
  · decide
