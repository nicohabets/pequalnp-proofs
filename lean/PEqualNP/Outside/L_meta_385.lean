import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_385

/-! The OR chain is handled exactly as in L-meta-374: after the chained OR gates the
accumulator wire carries the OR of v1 and rest, and old wires are unchanged. Two more gates
follow: the AND of t with that accumulator, and the OR of a with the AND. The chain lemma is
reused from L-meta-374; the helpers W, W_snoc, W_length and getD_snoc are copied from the
merged proof of L-meta-1321. -/
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

theorem acc_get (N v1 L k : ℕ) (hk : k < L) :
    (v1 :: (List.range L).map fun j => N + j).getD (k + 1) 0 = N + k := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem chain (B : List Bool) (N v1 : ℕ) (rest : List ℕ) (hB : B.length = N) (hv1 : v1 < N)
    (hr : ∀ w ∈ rest, w < N) :
    ∀ k ≤ rest.length,
      (W ((List.range k).map fun i => Gate.mk GateOp.or
        [(v1 :: (List.range rest.length).map fun j => N + j).getD i 0, rest.getD i 0]) B).length =
        N + k ∧
      (∀ j < N, (W ((List.range k).map fun i => Gate.mk GateOp.or
        [(v1 :: (List.range rest.length).map fun j => N + j).getD i 0, rest.getD i 0]) B).getD
        j false = B.getD j false) ∧
      (W ((List.range k).map fun i => Gate.mk GateOp.or
        [(v1 :: (List.range rest.length).map fun j => N + j).getD i 0, rest.getD i 0]) B).getD
        ((v1 :: (List.range rest.length).map fun j => N + j).getD k 0) false =
        ((v1 :: rest.take k).any fun w => B.getD w false) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [W, hB]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    have hk' : k < rest.length := by omega
    rw [List.range_succ, List.map_append, List.map_singleton, W_snoc]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, h1, List.length_singleton]; omega
    · intro j hj
      rw [getD_snoc, if_pos (by rw [h1]; omega)]
      exact h2 j hj
    · rw [acc_get N v1 rest.length k hk', getD_snoc, h1, if_neg (by omega), if_pos rfl]
      have hmem : rest.getD k 0 ∈ rest := by
        rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk'
      have hrd := h2 _ (hr _ hmem)
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        Bool.or_false, id]
      rw [h3, hrd, List.getD_eq_getElem _ _ hk', List.take_succ, List.getElem?_eq_getElem hk']
      simp only [Option.toList_some, List.cons_append, List.any_cons, List.any_append,
        List.any_nil, Bool.or_false, Bool.or_assoc]

theorem W_two (X : List Gate) (A B : Gate) (y : List Bool) :
    W (X ++ [A, B]) y =
      (W X y ++ [A.op.eval (A.inputs.map fun i => (W X y).getD i false)]) ++
        [B.op.eval (B.inputs.map fun i =>
          (W X y ++ [A.op.eval (A.inputs.map fun i => (W X y).getD i false)]).getD i false)] := by
  rw [List.append_cons _ _ [_], W_snoc, W_snoc]

end PEqualNP.Outside.L_meta_385

theorem PEqualNP.Outside.L_meta_385 :
∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : List Bool) (a t v1 : ℕ) (rest : List ℕ), a < (x.length + gs.length) → t < (x.length + gs.length) → v1 < (x.length + gs.length) → (∀ w ∈ rest, w < (x.length + gs.length)) → PEqualNP.CircuitLowerBounds.Circuit.eval (PEqualNP.CircuitLowerBounds.Circuit.mk (gs ++ ((List.range rest.length).map (fun i => PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(v1 :: (List.range rest.length).map (fun j => (x.length + gs.length) + j)).getD i 0, rest.getD i 0]) ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [t, (v1 :: (List.range rest.length).map (fun j => (x.length + gs.length) + j)).getD rest.length 0], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [a, (x.length + gs.length) + rest.length]])) ((x.length + gs.length) + rest.length + 1)) x = ((PEqualNP.CircuitLowerBounds.Circuit.wires (PEqualNP.CircuitLowerBounds.Circuit.mk gs o) x).getD a false || ((PEqualNP.CircuitLowerBounds.Circuit.wires (PEqualNP.CircuitLowerBounds.Circuit.mk gs o) x).getD t false && (v1 :: rest).any (fun w => (PEqualNP.CircuitLowerBounds.Circuit.wires (PEqualNP.CircuitLowerBounds.Circuit.mk gs o) x).getD w false)))
 := by
  open PEqualNP.Outside.L_meta_385 PEqualNP.CircuitLowerBounds in
  intro gs o x a t v1 rest ha ht hv1 hr
  have hwg : Circuit.wires (Circuit.mk gs o) x = W gs x := rfl
  have hWl : (W gs x).length = x.length + gs.length := W_length gs x
  obtain ⟨h1, h2, h3⟩ := chain (W gs x) (x.length + gs.length) v1 rest hWl hv1 hr rest.length
    le_rfl
  rw [Circuit.eval, Circuit.wires, List.foldl_append, ← W, ← W, W_two, hwg]
  generalize W ((List.range rest.length).map fun i => Gate.mk GateOp.or
    [(v1 :: (List.range rest.length).map fun j => (x.length + gs.length) + j).getD i 0,
      rest.getD i 0]) (W gs x) = B1 at h1 h2 h3 ⊢
  have ha' := h2 a ha
  have ht' := h2 t ht
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, id, getD_snoc,
    List.length_append, List.length_singleton, h1, lt_irrefl, if_false, if_true,
    show a < x.length + gs.length + rest.length by omega,
    show t < x.length + gs.length + rest.length by omega,
    show ¬ (x.length + gs.length + rest.length + 1 < x.length + gs.length + rest.length + 1) by omega,
    Nat.lt_succ_self, ha', ht', h3, List.take_length]
