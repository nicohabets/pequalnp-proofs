import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_5689 : PEqualNP.MetaComplexity.Monotone2 ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 1] }], output := 10 } : PEqualNP.CircuitLowerBounds.Circuit) ∧
  ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 1] }], output := 10 } : PEqualNP.CircuitLowerBounds.Circuit).size = 3 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 4 => (8191 : ℕ).testBit (4 * u.val + v.val)) ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 1] }], output := 10 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    fin_cases hg <;> simp
  · decide
  · decide
