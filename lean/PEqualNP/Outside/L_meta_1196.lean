import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1196

-- The chain of OR gates: gate 0 reads inputs 0 and 1, gate k > 0 reads gate k - 1 and
-- input k + 1, so gate k is the OR of the first k + 2 inputs.

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def prev (n k : ℕ) : ℕ := if k = 0 then 0 else n + k - 1

def gate (n k : ℕ) : Gate := ⟨GateOp.or, [prev n k, k + 1]⟩

def gs (n j : ℕ) : List Gate := (List.range j).map (gate n)

def chain (n : ℕ) : Circuit := ⟨gs n (n - 1), if n = 1 then 0 else n + (n - 2)⟩

theorem getD_eq (x : List Bool) (i : ℕ) (h : i < x.length) : x.getD i false = x[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem take_any (x : List Bool) (i : ℕ) (h : i < x.length) :
    (x.take (i + 1)).any id = ((x.take i).any id || x[i]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, List.any_append, List.any_cons, List.any_nil, Bool.or_false, id_eq]

theorem wires_gs (n : ℕ) (x : List Bool) (hx : x.length = n) :
    ∀ j, j + 1 ≤ n → wiresFrom (gs n j) x =
      x ++ (List.range j).map (fun k => (x.take (k + 2)).any id) := by
  intro j
  induction j with
  | zero => intro _; simp [gs, wiresFrom]
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    have hsplit : gs n (j + 1) = gs n j ++ [gate n j] := by
      simp [gs, List.range_succ]
    rw [hsplit]
    have : wiresFrom (gs n j ++ [gate n j]) x = wiresFrom [gate n j] (wiresFrom (gs n j) x) := by
      simp [wiresFrom, List.foldl_append]
    rw [this, ih']
    simp only [wiresFrom, List.foldl_cons, List.foldl_nil, List.range_succ, List.map_append,
      List.map_cons, List.map_nil, List.append_assoc]
    congr 2
    simp only [gate, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false, id_eq]
    have hW : ∀ i (hi : i < x.length), (x ++ List.map (fun k => (List.take (k + 2) x).any id)
        (List.range j)).getD i false = x[i]'hi := by
      intro i hi
      rw [List.getD_append _ _ _ _ hi, getD_eq x i hi]
    rw [hW (j + 1) (by omega)]
    have h2 := take_any x (j + 1) (by omega)
    rw [show j + 1 + 1 = j + 2 by omega] at h2
    rw [h2]
    congr 1
    unfold prev
    split_ifs with h0
    · subst h0
      rw [hW 0 (by omega)]
      rw [List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      simp
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by
        show n + j - 1 - x.length < j
        omega)]
      simp only [Option.map_some, Option.getD_some]
      rw [show n + j - 1 - x.length + 2 = j + 1 by omega]

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ C : Circuit, (∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧ C.size = n - 1 ∧ ∀ x : List Bool, x.length = n → (C.eval x = x.any id) := by
  intro n hn
  refine ⟨chain n, ?_, ?_, ?_⟩
  · intro g hg
    simp only [chain, gs, List.mem_map, List.mem_range] at hg
    obtain ⟨k, -, rfl⟩ := hg
    simp [gate]
  · simp [chain, Circuit.size, gs]
  · intro x hx
    have hw := wires_gs n x hx (n - 1) (by omega)
    unfold Circuit.eval Circuit.wires
    change (wiresFrom (gs n (n - 1)) x).getD (chain n).output false = _
    rw [hw]
    simp only [chain]
    split_ifs with h1
    · subst h1
      rw [List.getD_append _ _ _ _ (by omega), getD_eq x 0 (by omega)]
      match x, hx with
      | [a], _ => simp
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some]
      rw [show n + (n - 2) - x.length + 2 = x.length by omega, List.take_length]

end PEqualNP.Outside.L_meta_1196

theorem PEqualNP.Outside.L_meta_1196 : ∀ n : ℕ, 1 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧ C.size = n - 1 ∧ ∀ x : List Bool, x.length = n → (C.eval x = x.any id) :=
  PEqualNP.Outside.L_meta_1196.main
