import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_828

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem fan : FanInTwo ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem evalB : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    Circuit.eval ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit) [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b4) || (b2 && b3) || (b4 && b5)) := by
  decide +kernel

theorem ofFnN (x : Fin 6 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
  simp [List.ofFn_succ]

theorem edges (x : Fin 6 → Bool) :
    (((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 4) || (x 2 && x 3) || (x 4 && x 5)) = true ↔
      ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 4), (2, 3), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) := by
  constructor
  · intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ((((h | h) | h) | h) | h)
    · exact ⟨0, 1, by decide, h.1, h.2⟩
    · exact ⟨0, 2, by decide, h.1, h.2⟩
    · exact ⟨0, 4, by decide, h.1, h.2⟩
    · exact ⟨2, 3, by decide, h.1, h.2⟩
    · exact ⟨4, 5, by decide, h.1, h.2⟩
  · rintro ⟨u, v, hm, hu, hv⟩
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain rfl : u = 0 := Fin.ext h1
      obtain rfl : v = 1 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 0 := Fin.ext h1
      obtain rfl : v = 2 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 0 := Fin.ext h1
      obtain rfl : v = 4 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 2 := Fin.ext h1
      obtain rfl : v = 3 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 4 := Fin.ext h1
      obtain rfl : v = 5 := Fin.ext h2
      simp [hu, hv]

end PEqualNP.Outside.L_meta_828

theorem PEqualNP.Outside.L_meta_828 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 7 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 4), (2, 3), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨PEqualNP.Outside.L_meta_828.fan, rfl, fun x => ?_⟩
  rw [PEqualNP.Outside.L_meta_828.ofFnN, PEqualNP.Outside.L_meta_828.evalB]
  exact PEqualNP.Outside.L_meta_828.edges x
