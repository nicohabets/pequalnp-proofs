import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5014

/-! A monotone circuit is monotone in its inputs, and so is the extra wire `x 0 || x 1`.
Every input on which the edge function is true lies above one of the twelve listed edges, and
every input on which it is false lies below one of the twelve listed maximal false inputs
(checked over all 512 inputs by decide), so the circuit agrees with the edge function
everywhere. The wire-list helpers `W`, `W_snoc`, `W_length`, `getD_snoc`, `Le`, `eval_mono` and
`W_mono` are copied from the merged proof of L-meta-1321. -/

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
      simp [List.getElem?_cons, this]

/-- Pointwise order on wire lists (copied from L-meta-1321). -/
def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [if_pos h1] at ht ⊢; exact ih t ht
    · rw [if_neg h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [if_pos h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht

/-- The ten input wires. -/
def inp (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 1]

/-- An input given by a bit mask. -/
def bx (n : ℕ) : Fin 9 → Bool := fun k => n.testBit k.val

/-- The edge function. -/
def fE (x5 : Fin 9 → Bool) : Bool :=
  [((0 : Fin 9), (1 : Fin 9)), (1, 2), (2, 3), (0, 4), (3, 4), (0, 5), (1, 6), (2, 7), (5, 7),
    (3, 8), (5, 8), (6, 8)].any fun x6 : Fin 9 × Fin 9 => x5 x6.1 && x5 x6.2

theorem inp_le (x y : Fin 9 → Bool) (h : ∀ k, x k = true → y k = true) : Le (inp x) (inp y) := by
  intro i hi
  rw [inp, getD_snoc] at hi ⊢
  simp only [List.length_ofFn] at hi ⊢
  by_cases h1 : i < 9
  · rw [if_pos h1] at hi ⊢
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
    simp only [h1, List.ofFnNthVal, dite_true, Option.getD_some] at hi ⊢
    exact h _ hi
  · rw [if_neg h1] at hi ⊢
    by_cases h2 : i = 9
    · rw [if_pos h2] at hi ⊢
      simp only [Bool.or_eq_true] at hi ⊢
      exact hi.imp (h 0) (h 1)
    · rw [if_neg h2] at hi; simp at hi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem key : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    (fE ![b0, b1, b2, b3, b4, b5, b6, b7, b8] = false →
      ∃ M ∈ [(42 : ℕ), 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402],
        ∀ k : Fin 9, ![b0, b1, b2, b3, b4, b5, b6, b7, b8] k = true → bx M k = true) ∧
    (fE ![b0, b1, b2, b3, b4, b5, b6, b7, b8] = true →
      ∃ m ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320],
        ∀ k : Fin 9, bx m k = true → ![b0, b1, b2, b3, b4, b5, b6, b7, b8] k = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_5014

theorem PEqualNP.Outside.L_meta_5014 :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)], x1.eval ((List.ofFn fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5) ++ [x3.testBit (0 : ℕ) || x3.testBit (1 : ℕ)]) = Bool.true) → (∀ x4 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x1.eval ((List.ofFn fun (x6 : Fin (9 : ℕ)) => x4.testBit ↑x6) ++ [x4.testBit (0 : ℕ) || x4.testBit (1 : ℕ)]) = Bool.false) → ∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2 := by
  open PEqualNP.Outside.L_meta_5014 PEqualNP.CircuitLowerBounds in
  intro x1 hm ht hf x5
  have hm' : ∀ g ∈ x1.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hm g hg).1
    simpa using this
  have mono : ∀ x y : Fin 9 → Bool, (∀ k, x k = true → y k = true) →
      x1.eval (inp x) = true → x1.eval (inp y) = true := by
    intro x y hxy h
    exact W_mono x1.gates hm' (inp x) (inp y) (by simp [inp]) (inp_le x y hxy) _ h
  have hx : x5 = ![x5 0, x5 1, x5 2, x5 3, x5 4, x5 5, x5 6, x5 7, x5 8] := by
    funext k; fin_cases k <;> rfl
  obtain ⟨kf, kt⟩ := key (x5 0) (x5 1) (x5 2) (x5 3) (x5 4) (x5 5) (x5 6) (x5 7) (x5 8)
  rw [← hx] at kf kt
  show x1.eval (inp x5) = fE x5
  cases hfx : fE x5
  · obtain ⟨M, hM, hle⟩ := kf hfx
    have h0 : x1.eval (inp (bx M)) = false := hf M hM
    by_contra hne
    rw [Bool.not_eq_false] at hne
    rw [mono x5 (bx M) hle hne] at h0
    exact absurd h0 (by decide)
  · obtain ⟨m, hmem, hle⟩ := kt hfx
    exact mono (bx m) x5 hle (ht m hmem)
