import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_342

/-! Induction along the chain: after the first `k` chained OR gates the newest wire carries the
OR of `w0`, `w1` and the first `k` entries of `rest`, the old wires are unchanged, and every read
of an old wire sees its value in the old circuit. The helpers `W`, `W_snoc`, `W_length` and
`getD_snoc` are copied from the merged proof of L-meta-1321. -/

open PEqualNP.CircuitLowerBounds

/-- The wires of a gate list on an input (copied from L-meta-1321). -/
def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [this]

theorem chain (B : List Bool) (N : ℕ) (rest : List ℕ) (Wg : List Bool) (hB : B.length = N + 1)
    (hBo : ∀ j < N, B.getD j false = Wg.getD j false) (v0 : Bool) (hv0 : B.getD N false = v0)
    (hr : ∀ w ∈ rest, w < N) :
    ∀ k ≤ rest.length,
      (W ((List.range k).map fun i => Gate.mk GateOp.or [N + i, rest.getD i 0]) B).length =
        N + k + 1 ∧
      (∀ j < N, (W ((List.range k).map fun i => Gate.mk GateOp.or [N + i, rest.getD i 0]) B).getD
        j false = Wg.getD j false) ∧
      (W ((List.range k).map fun i => Gate.mk GateOp.or [N + i, rest.getD i 0]) B).getD (N + k)
        false = (v0 || (rest.take k).any fun w => Wg.getD w false) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [List.range_zero, List.map_nil, W, List.foldl_nil, List.take_zero, List.any_nil,
      Bool.or_false, Nat.add_zero]
    exact ⟨hB, hBo, hv0⟩
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    rw [List.range_succ, List.map_append, List.map_singleton, W_snoc]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, h1, List.length_singleton]; omega
    · intro j hj
      rw [getD_snoc, if_pos (by rw [h1]; omega)]
      exact h2 j hj
    · rw [getD_snoc, h1, if_neg (by omega), if_pos (by omega)]
      have hk' : k < rest.length := by omega
      have hmem : rest.getD k 0 ∈ rest := by
        rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk'
      have hrd : (W ((List.range k).map fun i => Gate.mk GateOp.or [N + i, rest.getD i 0]) B).getD
          (rest.getD k 0) false = Wg.getD (rest.getD k 0) false := h2 _ (hr _ hmem)
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        Bool.or_false, id]
      rw [h3, hrd, List.take_succ, List.any_append, List.getElem?_eq_getElem hk',
        List.getD_eq_getElem _ _ hk']
      simp [Bool.or_assoc]

end PEqualNP.Outside.L_meta_342

theorem PEqualNP.Outside.L_meta_342 :
∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : List Bool) (w0 w1 : ℕ) (rest : List ℕ), w0 < x.length + gs.length → w1 < x.length + gs.length → (∀ w ∈ rest, w < x.length + gs.length) → PEqualNP.CircuitLowerBounds.Circuit.eval (PEqualNP.CircuitLowerBounds.Circuit.mk (gs ++ (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [w0, w1] :: (List.range rest.length).map (fun i => PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [x.length + gs.length + i, rest.getD i 0]))) (x.length + gs.length + rest.length)) x = (w0 :: w1 :: rest).any (fun w => (PEqualNP.CircuitLowerBounds.Circuit.wires (PEqualNP.CircuitLowerBounds.Circuit.mk gs o) x).getD w false) := by
  open PEqualNP.Outside.L_meta_342 PEqualNP.CircuitLowerBounds in
  intro gs o x w0 w1 rest h0 h1 hr
  set N := x.length + gs.length with hN
  have hwg : Circuit.wires (Circuit.mk gs o) x = W gs x := rfl
  have hWl : (W gs x).length = N := by rw [W_length]
  set v0 := ((W gs x).getD w0 false || (W gs x).getD w1 false) with hv0
  have hfull : Circuit.wires (Circuit.mk (gs ++ (Gate.mk GateOp.or [w0, w1] ::
      (List.range rest.length).map (fun i => Gate.mk GateOp.or [x.length + gs.length + i,
        rest.getD i 0]))) (x.length + gs.length + rest.length)) x =
      W ((List.range rest.length).map fun i => Gate.mk GateOp.or [N + i, rest.getD i 0])
        (W gs x ++ [v0]) := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons]
    simp [W, hv0, GateOp.eval, hN]
  obtain ⟨-, -, h3⟩ := chain (W gs x ++ [v0]) N rest (W gs x) (by simp [hWl])
    (fun j hj => by rw [getD_snoc, if_pos (by rw [hWl]; exact hj)]) v0
    (by rw [getD_snoc, hWl, if_neg (lt_irrefl N), if_pos rfl]) hr rest.length le_rfl
  rw [Circuit.eval, hfull, hwg, h3, List.take_length]
  simp [hv0, Bool.or_assoc]
