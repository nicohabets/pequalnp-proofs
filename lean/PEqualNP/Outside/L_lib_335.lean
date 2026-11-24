import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_335 : PEqualNP.TwoColour.tCount 14
      (PEqualNP.CircuitLowerBounds.Circuit.mk [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 7]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 6]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [27, 11]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [30, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 22]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 34]⟩]
        40)
      (fun i => decide (7 ≤ i)) = 0 := by
  decide +kernel
