import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8756

/-! The hypotheses on gate 1 contradict each other. -/

end PEqualNP.Outside.L_meta_8756

theorem PEqualNP.Outside.L_meta_8756 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5 → x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5.inputs ≤ List.map (fun (x8 : ℕ) => [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x8 x8) x5.inputs → (∃ (x9 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x9 ∧ x9.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (16 : ℕ) ≤ x1.size := by
  intro x1 _ _ _ x5 h5 hop _ ⟨x9, h9, hop9⟩
  rw [h5] at h9
  cases h9
  rw [hop] at hop9
  cases hop9
