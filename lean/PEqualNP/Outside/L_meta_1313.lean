import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1313

/-! Induction along the gates, for two inputs of length n that agree at the unmarked positions: every wire of degree 0 has the same value on both. An input wire of degree 0 is unmarked (or missing); an AND gate of degree 0 has a zero sum, an OR gate of degree 0 a zero maximum, so every wire it reads has degree 0 and the same value on both inputs. The output has degree 0. -/

open PEqualNP.CircuitLowerBounds

theorem ld_snoc (gs : List Gate) (g : Gate) (o o' n : ℕ) (marked : Finset ℕ) :
    Circuit.lineDegrees ⟨gs ++ [g], o⟩ n marked =
      Circuit.lineDegrees ⟨gs, o'⟩ n marked ++
        [g.lineDegree (Circuit.lineDegrees ⟨gs, o'⟩ n marked)] := by
  simp [Circuit.lineDegrees, List.foldl_append]

theorem ld_length (gs : List Gate) (o n : ℕ) (marked : Finset ℕ) :
    (Circuit.lineDegrees ⟨gs, o⟩ n marked).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.lineDegrees]
  | append_singleton gs g ih => rw [ld_snoc _ _ _ o]; simp [ih]; omega

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

theorem w_snoc (gs : List Gate) (g : Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g], o⟩ x = Circuit.wires ⟨gs, o'⟩ x ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, o'⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem w_length (gs : List Gate) (o : ℕ) (x : List Bool) :
    (Circuit.wires ⟨gs, o⟩ x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih => rw [w_snoc _ _ _ o]; simp [ih]; omega

theorem le_foldr_max (l : List ℕ) (x : ℕ) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih hx) (le_max_right _ _)

theorem inputs_zero (g : Gate) (d : List ℕ) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : g.lineDegree d = 0) : ∀ j ∈ g.inputs, d.getD j 0 = 0 := by
  intro j hj
  have hm : d.getD j 0 ∈ g.inputs.map fun i => d.getD i 0 := List.mem_map.2 ⟨j, hj, rfl⟩
  unfold Gate.lineDegree at h
  rcases hop with hop | hop
  · rw [if_pos hop] at h
    exact (List.sum_eq_zero_iff.1 h) _ hm
  · rw [if_neg (by rw [hop]; simp)] at h
    have := le_foldr_max _ _ hm
    omega

theorem key (gs : List Gate) (o n : ℕ) (marked : Finset ℕ) (x x' : List Bool)
    (hx : x.length = n) (hx' : x'.length = n)
    (hagree : ∀ i < n, i ∉ marked → x.getD i false = x'.getD i false)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (Circuit.lineDegrees ⟨gs, o⟩ n marked).getD i 0 = 0 →
      (Circuit.wires ⟨gs, o⟩ x).getD i false = (Circuit.wires ⟨gs, o⟩ x').getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    simp only [Circuit.lineDegrees, Circuit.wires, List.foldl_nil] at hi ⊢
    by_cases hin : i < n
    · rw [List.getD_eq_getElem _ _ (by simp; omega)] at hi
      simp only [List.getElem_map, List.getElem_range] at hi
      exact hagree i hin (by intro hm; simp [hm] at hi)
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hmono g' (by simp [hg']))
    intro i hi
    rw [ld_snoc _ _ _ o, getD_snoc, ld_length] at hi
    rw [w_snoc _ _ _ o, w_snoc _ _ _ o, getD_snoc, getD_snoc, w_length, w_length, hx, hx']
    split_ifs at hi ⊢ with h1 h2
    · exact ih' i hi
    · have hz := inputs_zero g _ (hmono g (by simp)) hi
      congr 1
      exact List.map_congr_left (fun j hj => ih' j (hz j hj))
    · rfl

end PEqualNP.Outside.L_meta_1313

theorem PEqualNP.Outside.L_meta_1313 :
∀ (n : ℕ) (marked : Finset ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree n marked C 0 → ∀ z z2 : Fin n → Bool, (∀ i : Fin n, i.val ∉ marked → z i = z2 i) → PEqualNP.MetaComplexity.circuitFun n C z = PEqualNP.MetaComplexity.circuitFun n C z2 := by
  open PEqualNP.Outside.L_meta_1313 PEqualNP.CircuitLowerBounds in
  intro n marked C hC hD z z2 hz
  obtain ⟨gs, o⟩ := C
  have hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  have h0 : (Circuit.lineDegrees ⟨gs, o⟩ n marked).getD o 0 = 0 := by
    have : Circuit.lineDeg ⟨gs, o⟩ n marked ≤ 0 := hD
    exact Nat.le_zero.1 this
  unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval
  apply key gs o n marked _ _ (by simp) (by simp) _ hmono o h0
  intro i hi hm
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_ofFn]
  exact hz ⟨i, hi⟩ hm
