import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5212
open PEqualNP.CircuitLowerBounds

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

open PEqualNP.MetaComplexity in
def flipg (k : ℕ) (g : BinaryGate) : BinaryGate :=
  ⟨fun a b => g.op (a != decide (g.left = k)) (b != decide (g.right = k)), g.left, g.right⟩

theorem xx (a d : Bool) : ((a != d) != d) = a := by cases a <;> cases d <;> rfl

open PEqualNP.MetaComplexity in
theorem bsim (k : ℕ) : ∀ (gs : List BinaryGate) (U V : List Bool), U.length = V.length →
    k < U.length → (∀ i, V.getD i false = (U.getD i false != decide (i = k))) →
    ∀ i, ((gs.map (flipg k)).foldl
        (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) V).getD i false
      = ((gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) U).getD i false
          != decide (i = k)) := by
  intro gs
  induction gs with
  | nil => intro U V _ _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen hk h i
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have hv : (flipg k g).op (V.getD (flipg k g).left false) (V.getD (flipg k g).right false)
        = g.op (U.getD g.left false) (U.getD g.right false) := by
      show g.op (V.getD g.left false != decide (g.left = k)) (V.getD g.right false != decide (g.right = k)) = _
      rw [h g.left, h g.right, xx, xx]
    rw [hv]
    apply ih
    · rw [List.length_append, List.length_append, hlen]
    · rw [List.length_append]; exact Nat.lt_succ_of_lt hk
    · intro t
      rcases Nat.lt_trichotomy t U.length with h1 | h1 | h1
      · rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ h1]
        exact h t
      · have hd : decide (t = k) = false := decide_eq_false (by omega)
        rw [hd, h1]
        conv_lhs => rw [hlen]
        rw [getD_snoc_eq, getD_snoc_eq]
        cases g.op (U.getD g.left false) (U.getD g.right false) <;> rfl
      · have hd : decide (t = k) = false := decide_eq_false (by omega)
        rw [hd, getD_snoc_gt _ _ _ (by omega), getD_snoc_gt _ _ _ h1]
        rfl

end PEqualNP.Outside.L_meta_5212

open PEqualNP.Outside.L_meta_5212 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_5212 : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : ℕ) (x3 : Bool), (∀ x4 ∈ x1.gates, ∃ (x6 : Bool) (x7 : Bool), x4.op = fun (x8 x9 : Bool) => x8 == x6 && x9 == x7) → ∃ (x5 : PEqualNP.MetaComplexity.BinaryCircuit), x5.size = x1.size ∧ x5.output = x1.output ∧ (∀ x6 ∈ x5.gates, ∃ (x8 : Bool) (x9 : Bool), x6.op = fun (x10 x11 : Bool) => x10 == x8 && x11 == x9) ∧ ∀ (x6 x7 : List Bool), x6.length = x7.length → x2 < x6.length → (∀ (x10 : ℕ), x7.getD x10 Bool.false = (x6.getD x10 Bool.false != Decidable.decide (x10 = x2))) → (x5.eval x7 != (x3 != Decidable.decide (x1.output = x2))) = (x1.eval x6 != x3) := by
  intro C k b hform
  refine ⟨⟨C.gates.map (flipg k), C.output⟩, ?_, rfl, ?_, ?_⟩
  · show (C.gates.map (flipg k)).length = C.gates.length
    rw [List.length_map]
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    obtain ⟨p, q, hop⟩ := hform g0 hg0
    refine ⟨p != decide (g0.left = k), q != decide (g0.right = k), ?_⟩
    show (fun a b => g0.op (a != decide (g0.left = k)) (b != decide (g0.right = k))) = _
    rw [hop]
    funext a b
    generalize decide (g0.left = k) = dl
    generalize decide (g0.right = k) = dr
    cases a <;> cases b <;> cases p <;> cases q <;> cases dl <;> cases dr <;> rfl
  · intro U V hlen hk hrel
    have h := bsim k C.gates U V hlen hk hrel C.output
    show (((C.gates.map (flipg k)).foldl
        (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) V).getD C.output false
          != (b != decide (C.output = k)))
      = ((C.gates.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) U).getD
          C.output false != b)
    rw [h]
    generalize decide (C.output = k) = d
    generalize (C.gates.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) U).getD
      C.output false = c
    cases c <;> cases b <;> cases d <;> rfl
