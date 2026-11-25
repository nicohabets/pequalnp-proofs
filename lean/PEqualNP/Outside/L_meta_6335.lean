import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6335

/-! Rewire: every read of wire 10 (and the output, if it is wire 10) is sent to wire `i`, or,
when `i = 10`, to a wire index past the end of the circuit, which always reads false. Gates,
operations and fan-in are unchanged, and by induction along the gate list each wire of the new
circuit on `x ++ [b]` carries the value of the matching wire of the old circuit on
`x ++ [x.getD i false]`. The helpers `W`, `W_snoc`, `W_length` and `getD_snoc` are copied from
the merged proof of L-meta-1321. -/

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

theorem getD_big (l : List Bool) (t : ℕ) (h : l.length ≤ t) : l.getD t false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- The wire map: wire 10 goes to `s`, every other wire stays. -/
def sig (s k : ℕ) : ℕ := if k = 10 then s else k

/-- The rewired gate. -/
def rg (s : ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map (sig s) }

theorem sig_ten (s : ℕ) : sig s 10 = s := if_pos rfl

theorem sig_ne (s k : ℕ) (h : k ≠ 10) : sig s k = k := if_neg h

theorem inv (s : ℕ) (L : List Bool) (b c : Bool) (hL : L.length = 10)
    (hc : (s < 10 → c = L.getD s false) ∧ (¬ s < 10 → c = false))
    (gs : List Gate) (hN : s < 10 ∨ 11 + gs.length ≤ s) :
    ∀ k, (W (gs.map (rg s)) (L ++ [b])).getD (sig s k) false = (W gs (L ++ [c])).getD k false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k
    simp only [List.map_nil, W, List.foldl_nil]
    by_cases hk : k = 10
    · subst hk
      rw [sig_ten, getD_snoc, getD_snoc, hL, if_neg (lt_irrefl 10), if_pos rfl]
      by_cases h1 : s < 10
      · rw [if_pos h1, hc.1 h1]
      · rw [hc.2 h1, if_neg h1, if_neg (by simp at hN; omega)]
    · rw [sig_ne s k hk, getD_snoc, getD_snoc, hL]
      simp [hk]
  | append_singleton gs g ih =>
    have ih := ih (by rcases hN with h | h; exact Or.inl h; right; simp at h; omega)
    intro k
    rw [List.map_append, List.map_singleton, W_snoc, W_snoc]
    have hv : (rg s g).op.eval ((rg s g).inputs.map fun i =>
        (W (gs.map (rg s)) (L ++ [b])).getD i false) =
        g.op.eval (g.inputs.map fun i => (W gs (L ++ [c])).getD i false) := by
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact ih i
    have hl1 : (W (gs.map (rg s)) (L ++ [b])).length = 11 + gs.length := by
      simp only [W_length, List.length_append, hL, List.length_map, List.length_singleton]
    have hl2 : (W gs (L ++ [c])).length = 11 + gs.length := by
      simp only [W_length, List.length_append, hL, List.length_singleton]
    have hgl : (gs ++ [g]).length = gs.length + 1 := by simp
    rw [hv, getD_snoc, getD_snoc, hl1, hl2]
    by_cases hk : k = 10
    · subst hk
      have e := ih 10
      rw [sig_ten] at e ⊢
      rw [if_pos (by omega : (10 : ℕ) < 11 + gs.length)]
      by_cases h1 : s < 10
      · rw [if_pos (by omega), e]
      · have h2 : 11 + (gs.length + 1) ≤ s := by
          rcases hN with h | h
          · exact absurd h h1
          · rw [hgl] at h; omega
        rw [if_neg (by omega), if_neg (by omega), ← e, getD_big _ _ (by rw [hl1]; omega)]
    · have e := ih k
      rw [sig_ne s k hk] at e ⊢
      by_cases h1 : k < 11 + gs.length
      · rw [if_pos h1, if_pos h1, e]
      · rw [if_neg h1, if_neg h1]

end PEqualNP.Outside.L_meta_6335

theorem PEqualNP.Outside.L_meta_6335 :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → ∀ (x3 : Fin (11 : ℕ)), ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size = x1.size ∧ ∀ (x5 : List Bool) (x6 : Bool), x5.length = (10 : ℕ) → x4.eval (x5 ++ [x6]) = x1.eval (x5 ++ [x5.getD (↑x3) Bool.false]) := by
  open PEqualNP.Outside.L_meta_6335 PEqualNP.CircuitLowerBounds in
  intro x1 hfan x3
  set s : ℕ := if x3.val < 10 then x3.val else 11 + x1.gates.length with hsdef
  refine ⟨{ gates := x1.gates.map (rg s), output := sig s x1.output }, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
    exact ⟨(hfan g hg).1, by simpa [rg] using (hfan g hg).2⟩
  · simp [Circuit.size]
  · intro L b hL
    have hc : (s < 10 → L.getD x3.val false = L.getD s false) ∧
        (¬ s < 10 → L.getD x3.val false = false) := by
      constructor
      · intro h
        by_cases h3 : x3.val < 10
        · rw [hsdef, if_pos h3]
        · rw [hsdef, if_neg h3] at h; omega
      · intro h
        by_cases h3 : x3.val < 10
        · rw [hsdef, if_pos h3] at h; exact absurd h3 h
        · exact getD_big _ _ (by have := x3.isLt; omega)
    have hN : s < 10 ∨ 11 + x1.gates.length ≤ s := by
      by_cases h3 : x3.val < 10
      · left; rw [hsdef, if_pos h3]; exact h3
      · right; rw [hsdef, if_neg h3]
    exact inv s L b _ hL ⟨fun h => (hc.1 h), fun h => hc.2 h⟩ x1.gates hN x1.output
