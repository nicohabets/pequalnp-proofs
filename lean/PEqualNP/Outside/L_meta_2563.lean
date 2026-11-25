import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2563

-- Vacuous case: the circuit has exactly two gates. Gate 0 is x0 OR x4 by hypothesis and gate 1
-- reads at most two wires, so some vertex v outside {0, 4} is read by no gate. Two inputs that
-- differ only at v (a single neighbour u of v, and u together with v) get the same value at
-- every wire other than v, but the edge function separates them; if the output is wire v itself,
-- the input with only v on is accepted although it has no edge.

open PEqualNP.CircuitLowerBounds

def F (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def single (u : Fin 9) : Fin 9 → Bool := fun i => decide (i = u)

def pair (u v : Fin 9) : Fin 9 → Bool := fun i => decide (i = u ∨ i = v)

theorem sep : ∀ v : Fin 9, ∃ u : Fin 9, u ≠ v ∧ F (single u) = false ∧ F (pair u v) = true := by
  decide

theorem single_false : ∀ v : Fin 9, F (single v) = false := by decide

theorem pick (l : List ℕ) (hl : l.length ≤ 2) : ∃ v ∈ ([1, 2, 3, 5, 6] : List ℕ), v ∉ l := by
  by_contra h
  push_neg at h
  have hsub : ({1, 2, 3, 5, 6} : Finset ℕ) ⊆ l.toFinset := by
    intro v hv
    rw [List.mem_toFinset]
    apply h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have h1 := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le l
  have h3 : ({1, 2, 3, 5, 6} : Finset ℕ).card = 5 := by decide
  omega

theorem getD_ofFn (x : Fin 9 → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < 9 then x ⟨i, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i < 9 <;> simp [h]

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem main (C : Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (h9 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4))
    (hf : PEqualNP.MetaComplexity.circuitFun 9 C = F)
    (h1 : Option.map (fun g : Gate => g.op) C.gates[1]? = some GateOp.and)
    (h2 : C.gates[2]? = none) : False := by
  obtain ⟨gs, out⟩ := C
  simp only at h1 h2 hfan h9 hf
  -- the gate list has exactly two gates
  rcases gs with _ | ⟨g0, _ | ⟨g1, _ | ⟨g2, gs⟩⟩⟩
  · simp at h1
  · simp at h1
  swap
  · simp at h2
  have hg1 : g1 ∈ [g0, g1] := by simp
  have hlen := (hfan g1 hg1).2
  let e0 : (Fin 9 → Bool) → Bool := fun z =>
    g0.op.eval (g0.inputs.map fun i => (List.ofFn z).getD i false)
  let e1 : (Fin 9 → Bool) → Bool := fun z =>
    g1.op.eval (g1.inputs.map fun i => (List.ofFn z ++ [e0 z]).getD i false)
  have hW : ∀ z : Fin 9 → Bool, Circuit.wires ⟨[g0, g1], out⟩ (List.ofFn z) =
      (List.ofFn z ++ [e0 z]) ++ [e1 z] := by
    intro z; rfl
  have he0 : ∀ z : Fin 9 → Bool, e0 z = (z 0 || z 4) := by
    intro z
    have := h9 z
    rw [hW z, getD_snoc, if_neg (by simp), getD_snoc, if_pos (by simp)] at this
    exact this
  have hev : ∀ z : Fin 9 → Bool, F z = ((List.ofFn z ++ [e0 z]) ++ [e1 z]).getD out false := by
    intro z
    rw [← hf]
    show Circuit.eval ⟨[g0, g1], out⟩ (List.ofFn z) = _
    unfold Circuit.eval
    rw [hW z]
  obtain ⟨w, hwmem, hwnot⟩ := pick g1.inputs hlen
  have hw9 : w < 9 := by simp at hwmem; omega
  have hw04 : w ≠ 0 ∧ w ≠ 4 := by simp at hwmem; omega
  set v : Fin 9 := ⟨w, hw9⟩ with hv
  -- inputs that agree off v agree on every wire other than v
  have agree : ∀ z z' : Fin 9 → Bool, (∀ i : Fin 9, i ≠ v → z i = z' i) →
      ∀ i, i ≠ w → ((List.ofFn z ++ [e0 z]) ++ [e1 z]).getD i false =
        ((List.ofFn z' ++ [e0 z']) ++ [e1 z']).getD i false := by
    intro z z' hzz
    have h0 : e0 z = e0 z' := by
      rw [he0, he0, hzz 0 (by intro h; apply hw04.1; rw [hv] at h; exact (congrArg Fin.val h).symm),
        hzz 4 (by intro h; apply hw04.2; rw [hv] at h; exact (congrArg Fin.val h).symm)]
    have hA : ∀ i, i ≠ w → (List.ofFn z ++ [e0 z]).getD i false =
        (List.ofFn z' ++ [e0 z']).getD i false := by
      intro i hi
      rw [getD_snoc, getD_snoc, List.length_ofFn, List.length_ofFn, h0, getD_ofFn, getD_ofFn]
      split_ifs with ha hb
      all_goals first
        | rfl
        | (apply hzz; intro h; apply hi; rw [hv] at h; exact (congrArg Fin.val h))
    have h1' : e1 z = e1 z' := by
      show g1.op.eval _ = g1.op.eval _
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hA i (fun h => hwnot (h ▸ hi))
    intro i hi
    have key : ∀ (A : List Bool) (a b : Bool), ((A ++ [a]) ++ [b]).getD i false =
        if i = A.length + 1 then b else (A ++ [a]).getD i false := by
      intro A a b; rw [getD_snoc]; simp
    rw [key, key, List.length_ofFn, List.length_ofFn, h1']
    split_ifs
    · rfl
    · exact hA i hi
  by_cases hout : out = w
  · -- the output is the input wire v
    have := hev (single v)
    rw [single_false, hout, List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ (by simp; omega), getD_ofFn, dif_pos hw9] at this
    simp [single, hv] at this
  · obtain ⟨u, huv, hu1, hu2⟩ := sep v
    have hx := hev (single u)
    have hy := hev (pair u v)
    rw [agree (single u) (pair u v) (by
      intro i hi
      simp only [single, pair]
      by_cases h : i = u <;> simp [h, hi]) out hout] at hx
    rw [← hx, hu1, hu2] at hy
    exact Bool.false_ne_true hy.symm

end PEqualNP.Outside.L_meta_2563

theorem PEqualNP.Outside.L_meta_2563 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.and → x1.gates[(2 : ℕ)]? = Option.none → (16 : ℕ) ≤ x1.size :=
  fun C hfan h9 hf h1 h2 => (PEqualNP.Outside.L_meta_2563.main C hfan h9 hf h1 h2).elim
