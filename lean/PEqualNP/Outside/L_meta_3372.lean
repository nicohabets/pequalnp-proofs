import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3372
open PEqualNP.CircuitLowerBounds

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

def fl (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [F w g]) w

theorem fl_append (F : List Bool → Gate → Bool) (a b : List Gate) (w : List Bool) :
    fl F (a ++ b) w = fl F b (fl F a w) := by
  simp [fl, List.foldl_append]

theorem fl_cons (F : List Bool → Gate → Bool) (g : Gate) (gs : List Gate) (w : List Bool) :
    fl F (g :: gs) w = fl F gs (w ++ [F w g]) := rfl

theorem fl_len (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ w : List Bool, (fl F gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [fl_cons, ih]
    simp
    omega

theorem fl_keep (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (fl F gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [fl_cons, ih _ _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem fl_at (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) (k : ℕ)
    (hk : k < gs.length) :
    (fl F gs w).getD (w.length + k) false = F (fl F (gs.take k) w) gs[k] ∧
      ∀ a, a < w.length + k → (fl F gs w).getD a false = (fl F (gs.take k) w).getD a false := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hlen : (fl F (gs.take k) w).length = w.length + k := by
    rw [fl_len, List.length_take, Nat.min_eq_left (le_of_lt hk)]
  have e : fl F gs w = fl F (gs.drop (k + 1))
      (fl F (gs.take k) w ++ [F (fl F (gs.take k) w) gs[k]]) := by
    conv_lhs => rw [hsplit]
    rw [fl_append, fl_cons]
  constructor
  · rw [e, fl_keep _ _ _ _ (by simp; omega), ← hlen]
    simp
  · intro a ha
    rw [e, fl_keep _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

def EV (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem fl_snoc (F : List Bool → Gate → Bool) (l : List Gate) (g : Gate) (w : List Bool) :
    fl F (l ++ [g]) w = fl F l w ++ [F (fl F l w) g] := by
  rw [fl_append]; rfl

theorem two_count (p : Gate → Bool) (l : List Gate) (a b : ℕ) (hab : a < b) (hb : b < l.length)
    (pa : p (l[a]'(lt_trans hab hb)) = true) (pb : p l[b] = true) : 2 ≤ List.countP p l := by
  have ha : a < l.length := lt_trans hab hb
  have h1 : List.countP p l = List.countP p (l.take a) + List.countP p (l.drop a) := by
    rw [← List.countP_append, List.take_append_drop]
  have hd : b - (a + 1) < (l.drop (a + 1)).length := by rw [List.length_drop]; omega
  have hmem : l[b] ∈ l.drop (a + 1) := by
    have h5 : (l.drop (a + 1))[b - (a + 1)]'hd = l[b] := by
      rw [List.getElem_drop]; congr 1; omega
    rw [← h5]; exact List.getElem_mem hd
  have h3 : 0 < List.countP p (l.drop (a + 1)) := List.countP_pos_iff.2 ⟨l[b], hmem, pb⟩
  rw [h1, List.drop_eq_getElem_cons ha, List.countP_cons_of_pos pa]
  omega

theorem key (C : Circuit) (v k : ℕ) (a b : List Bool) (hlen : a.length = b.length)
    (hab : ∀ i, i ≠ v → a.getD i false = b.getD i false)
    (hfil : List.countP (fun g : Gate => decide (v ∈ g.inputs)) C.gates = 1)
    (hk : k < C.gates.length) (hread : v ∈ (C.gates[k]).inputs)
    (heq : (fl EV C.gates a).getD (a.length + k) false = (fl EV C.gates b).getD (a.length + k) false) :
    ∀ m, m ≤ C.gates.length → ∀ i, i ≠ v →
      (fl EV (C.gates.take m) a).getD i false = (fl EV (C.gates.take m) b).getD i false := by
  intro m
  induction m with
  | zero => intro _ i hi; exact hab i hi
  | succ m ih =>
    intro hm i hi
    have hm' : m < C.gates.length := hm
    have ih' := ih (le_of_lt hm')
    have hA : (fl EV (C.gates.take m) a).length = a.length + m := by
      rw [fl_len, List.length_take, Nat.min_eq_left (le_of_lt hm')]
    have hB : (fl EV (C.gates.take m) b).length = a.length + m := by
      rw [fl_len, List.length_take, Nat.min_eq_left (le_of_lt hm'), hlen]
    have hv : EV (fl EV (C.gates.take m) a) C.gates[m] = EV (fl EV (C.gates.take m) b) C.gates[m] := by
      by_cases hr : v ∈ (C.gates[m]).inputs
      · have hmk : m = k := by
          by_contra hne
          have pa : (fun g : Gate => decide (v ∈ g.inputs)) C.gates[m] = true := decide_eq_true hr
          have pb : (fun g : Gate => decide (v ∈ g.inputs)) C.gates[k] = true := decide_eq_true hread
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · have := two_count (fun g : Gate => decide (v ∈ g.inputs)) C.gates m k h hk pa pb
            omega
          · have := two_count (fun g : Gate => decide (v ∈ g.inputs)) C.gates k m h hm' pb pa
            omega
        subst hmk
        have e1 := (fl_at EV C.gates a m hm').1
        have e2 := (fl_at EV C.gates b m hm').1
        rw [← hlen] at e2
        rw [← e1, ← e2]
        exact heq
      · show (C.gates[m]).op.eval ((C.gates[m]).inputs.map fun i => (fl EV (C.gates.take m) a).getD i false)
          = (C.gates[m]).op.eval ((C.gates[m]).inputs.map fun i => (fl EV (C.gates.take m) b).getD i false)
        congr 1
        apply List.map_congr_left
        intro j hj
        apply ih'
        intro hjv
        rw [hjv] at hj
        exact hr hj
    rw [List.take_succ_eq_append_getElem hm', fl_snoc, fl_snoc]
    rcases Nat.lt_trichotomy i (a.length + m) with h | h | h
    · rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
      exact ih' i hi
    · rw [h]
      conv_lhs => rw [← hA]
      conv_rhs => rw [← hB]
      rw [getD_snoc_eq, getD_snoc_eq]
      exact hv
    · rw [getD_snoc_gt _ _ _ (by omega), getD_snoc_gt _ _ _ (by omega)]

end PEqualNP.Outside.L_meta_3372

open PEqualNP.Outside.L_meta_3372 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3372 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ) (x4 x5 : List Bool), x4.length = x5.length → x1.output ≠ x2 → (∀ (x8 : ℕ), x8 ≠ x2 → x4.getD x8 Bool.false = x5.getD x8 Bool.false) → (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (x2 ∈ x9.inputs)) x1.gates).length = (1 : ℕ) → x3 < x1.gates.length → x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).inputs → x1.eval x4 ≠ x1.eval x5 → { gates := x1.gates, output := x4.length + x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval x4 ≠ { gates := x1.gates, output := x4.length + x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval x5 := by
  intro C v k a b hlen hout hab hfil hk hread hne heq
  apply hne
  have hfil' : List.countP (fun g : Gate => decide (v ∈ g.inputs)) C.gates = 1 := by
    rw [List.countP_eq_length_filter]; exact hfil
  rw [gateAt_eq C k hk] at hread
  have heq' : (fl EV C.gates a).getD (a.length + k) false = (fl EV C.gates b).getD (a.length + k) false := heq
  have h := key C v k a b hlen hab hfil' hk hread heq' C.gates.length (le_refl _) C.output hout
  rw [List.take_length] at h
  exact h
