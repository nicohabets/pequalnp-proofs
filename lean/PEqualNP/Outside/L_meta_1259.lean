import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1259

/-! The star circuit is given in the statement; both sides are checked on all inputs by kernel evaluation. -/

end PEqualNP.Outside.L_meta_1259

theorem PEqualNP.Outside.L_meta_1259 :
∀ (x : Fin 6 → Bool) (y : Fin 3 → Bool), ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 17]⟩], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x ++ List.ofFn y) = decide (∃ (p : Fin 6) (w : Fin 3), (fun (p : Fin 6) (w : Fin 3) => decide ((p.val, w.val) ∈ ([(0, 0), (3, 0), (1, 0), (1, 1), (4, 1), (2, 1), (2, 2), (5, 2), (0, 2)] : List (ℕ × ℕ)))) p w = true ∧ x p = true ∧ y w = true) := by
  set_option synthInstance.maxSize 100000 in
  set_option synthInstance.maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  decide +kernel
