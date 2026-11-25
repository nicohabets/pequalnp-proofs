import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9199

-- The prefix lemmas for the gate fold are adapted from the merged L-meta-9299
-- by Junyoung Park (wiresFrom, wiresFrom_append, wiresFrom_prefix, getD_snoc).

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem main (C : Circuit) (x : Fin 14 → Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hin : ∀ i ∈ g.inputs, i < 14 + j) :
    PEqualNP.CleanedNonEdge.wireVal 14 C (14 + j) x =
      g.op.eval (g.inputs.map fun i => PEqualNP.CleanedNonEdge.wireVal 14 C i x) := by
  obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp hg
  have hsplit : C.gates = C.gates.take j ++ ([g] ++ C.gates.drop (j + 1)) := by
    rw [← hgj]
    conv_lhs => rw [← List.take_append_drop j C.gates, List.drop_eq_getElem_cons hj]
    rfl
  set P := wiresFrom (C.gates.take j) (List.ofFn x) with hPdef
  have hP : P.length = 14 + j := by
    rw [hPdef, length_wiresFrom, List.length_take, List.length_ofFn, Nat.min_eq_left hj.le]
  set e := g.op.eval (g.inputs.map fun i => P.getD i false) with he
  have hW : C.wires (List.ofFn x) = wiresFrom (C.gates.drop (j + 1)) (P ++ [e]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_append]
    rfl
  obtain ⟨t, ht, -⟩ := wiresFrom_prefix (C.gates.drop (j + 1)) (P ++ [e])
  have key : ∀ i, i < 14 + j + 1 →
      PEqualNP.CleanedNonEdge.wireVal 14 C i x = (P ++ [e]).getD i false := by
    intro i hi
    unfold PEqualNP.CleanedNonEdge.wireVal
    rw [hW, ht, List.getD_append _ _ _ _ (by simp; omega)]
  rw [key _ (by omega), getD_snoc, if_pos hP.symm, he]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := hin i hi
  rw [key i (by omega), getD_snoc, if_neg (by omega)]

end PEqualNP.Outside.L_meta_9199

theorem PEqualNP.Outside.L_meta_9199 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (14 : ℕ) → Bool) (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (∀ x6 ∈ x4.inputs, x6 < (14 : ℕ) + x3) → PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 ((14 : ℕ) + x3) x2 = x4.op.eval (List.map (fun (x7 : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x7 x2) x4.inputs) :=
  fun C x j g hg hin => PEqualNP.Outside.L_meta_9199.main C x j g hg hin
