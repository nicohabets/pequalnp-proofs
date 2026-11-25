import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8742

/-! A one-gate circuit outputs a function of at most two of the eleven wires. For every two
wires there are two inputs, differing in one bit, that agree on both wires but not on the
edge function, so the circuit is wrong on one of them. -/

/-- The edge function of the Petersen graph minus a vertex. -/
def pf (x6 : Fin 9 → Bool) : Bool :=
  x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 ||
    x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 || x6 5 && x6 7 ||
    x6 6 && x6 8 || x6 8 && x6 5

/-- The eleven input wires. -/
def inp (x6 : Fin 9 → Bool) : List Bool := List.ofFn x6 ++ [x6 0 && x6 2, true]

/-- An input given by a bit mask. -/
def bx (n : ℕ) : Fin 9 → Bool := fun k => n.testBit k.val

theorem collide : ∀ a b : Fin 12, ∃ p ∈ [((1 : ℕ), (17 : ℕ)), (4, 6), (0, 33)],
    (inp (bx p.1)).getD a.val false = (inp (bx p.2)).getD a.val false ∧
    (inp (bx p.1)).getD b.val false = (inp (bx p.2)).getD b.val false ∧
    pf (bx p.1) ≠ pf (bx p.2) := by
  decide +kernel

theorem getD_min (x : Fin 9 → Bool) (a : ℕ) :
    (inp x).getD a false = (inp x).getD (min a 11) false := by
  have hl : (inp x).length = 11 := by simp [inp]
  by_cases h : a < 11
  · rw [Nat.min_eq_left h.le]
  · rw [Nat.min_eq_right (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

end PEqualNP.Outside.L_meta_8742

theorem PEqualNP.Outside.L_meta_8742 :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (0 : ℕ) < x1.size → x1.size ≤ (13 : ℕ) → x1.gates[(1 : ℕ)]? = Option.none → ∃ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)), Bool.true]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  open PEqualNP.Outside.L_meta_8742 PEqualNP.CircuitLowerBounds in
  intro x1 hfan hpos _ hnone
  obtain ⟨g, hg⟩ : ∃ g, x1.gates = [g] := by
    rcases hl : x1.gates with _ | ⟨g, _ | ⟨g2, t⟩⟩
    · simp [Circuit.size, hl] at hpos
    · exact ⟨g, rfl⟩
    · simp [hl] at hnone
  have hlen : g.inputs.length ≤ 2 := (hfan g (by simp [hg])).2
  have hL : ∀ x : Fin 9 → Bool, (inp x).length = 11 := fun x => by simp [inp]
  have hev : ∀ x : Fin 9 → Bool, x1.eval (inp x) =
      (inp x ++ [g.op.eval (g.inputs.map fun i => (inp x).getD i false)]).getD x1.output false := by
    intro x
    simp only [Circuit.eval, Circuit.wires, hg, List.foldl]
  obtain ⟨F, a, b, hF⟩ : ∃ (F : Bool → Bool → Bool) (a b : ℕ), ∀ x : Fin 9 → Bool,
      x1.eval (inp x) = F ((inp x).getD a false) ((inp x).getD b false) := by
    by_cases ho : x1.output < 11
    · refine ⟨fun p _ => p, x1.output, x1.output, fun x => ?_⟩
      rw [hev, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [hL]; exact ho)]
    · by_cases ho' : x1.output = 11
      · have hv : ∀ x : Fin 9 → Bool, x1.eval (inp x) =
            g.op.eval (g.inputs.map fun i => (inp x).getD i false) := by
          intro x
          rw [hev, ho', List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hL]),
            hL]
          rfl
        rcases hi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
        · exact ⟨fun _ _ => g.op.eval [], 0, 0, fun x => by rw [hv, hi]; rfl⟩
        · exact ⟨fun p _ => g.op.eval [p], a, a, fun x => by rw [hv, hi]; rfl⟩
        · exact ⟨fun p q => g.op.eval [p, q], a, b, fun x => by rw [hv, hi]; rfl⟩
        · rw [hi] at hlen; simp at hlen
      · refine ⟨fun _ _ => false, 0, 0, fun x => ?_⟩
        rw [hev, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hL]; omega)]
        rfl
  obtain ⟨p, -, h1, h2, h3⟩ := collide ⟨min a 11, by omega⟩ ⟨min b 11, by omega⟩
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  apply h3
  have e1 := hcon (bx p.1)
  have e2 := hcon (bx p.2)
  change x1.eval (inp (bx p.1)) = pf (bx p.1) at e1
  change x1.eval (inp (bx p.2)) = pf (bx p.2) at e2
  rw [← e1, ← e2, hF, hF, getD_min _ a, getD_min _ b, getD_min (bx p.2) a, getD_min (bx p.2) b]
  simp only at h1 h2
  rw [h1, h2]
