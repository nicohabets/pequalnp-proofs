import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1268

/-! The star circuit is given in the statement; both sides are checked on all inputs by kernel evaluation. -/

end PEqualNP.Outside.L_meta_1268

theorem PEqualNP.Outside.L_meta_1268 :
∀ (x : Fin 3 → Bool) (y : Fin 3 → Bool), ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x ++ List.ofFn y) = decide (∃ (p : Fin 3) (w : Fin 3), (fun (p : Fin 3) (w : Fin 3) => decide ((p.val, w.val) ∈ ([(0, 0), (1, 0), (1, 1), (2, 1), (2, 2), (0, 2)] : List (ℕ × ℕ)))) p w = true ∧ x p = true ∧ y w = true) := by
  set_option synthInstance.maxSize 100000 in
  set_option synthInstance.maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  decide +kernel
