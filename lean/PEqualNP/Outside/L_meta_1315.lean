import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1315

/-! By induction along the gates, the degree list over the smaller marked set is entrywise at most the one over the larger set: input degrees are monotone in the marked set, and the degree of a gate (a sum or a maximum of entries read from the list) is monotone in the list. The two lists have the same length, so the new entries line up. -/

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

theorem sum_mono (is : List ℕ) (f f' : ℕ → ℕ) (h : ∀ i, f i ≤ f' i) :
    (is.map f).sum ≤ (is.map f').sum := by
  induction is with
  | nil => simp
  | cons a is ih => simp only [List.map_cons, List.sum_cons]; exact Nat.add_le_add (h a) ih

theorem max_mono (is : List ℕ) (f f' : ℕ → ℕ) (h : ∀ i, f i ≤ f' i) :
    (is.map f).foldr max 0 ≤ (is.map f').foldr max 0 := by
  induction is with
  | nil => simp
  | cons a is ih => simp only [List.map_cons, List.foldr_cons]; exact max_le_max (h a) ih

theorem gate_mono (g : Gate) (d d' : List ℕ) (h : ∀ i, d.getD i 0 ≤ d'.getD i 0) :
    g.lineDegree d ≤ g.lineDegree d' := by
  unfold Gate.lineDegree
  split_ifs
  · exact sum_mono _ _ _ h
  · exact max_mono _ _ _ h

theorem ld_mono (gs : List Gate) (o n : ℕ) (marked marked2 : Finset ℕ) (hsub : marked ⊆ marked2) :
    ∀ i, (Circuit.lineDegrees ⟨gs, o⟩ n marked).getD i 0 ≤
      (Circuit.lineDegrees ⟨gs, o⟩ n marked2).getD i 0 := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    simp only [Circuit.lineDegrees, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (List.range n)[i]? with
    | none => simp
    | some j =>
      simp only [Option.map_some, Option.getD_some]
      by_cases h : j ∈ marked
      · simp [h, hsub h]
      · simp only [h, if_false]; exact Nat.zero_le _
  | append_singleton gs g ih =>
    intro i
    rw [ld_snoc _ _ _ o, ld_snoc _ _ _ o, getD_snoc, getD_snoc, ld_length, ld_length]
    split_ifs
    · exact ih i
    · exact gate_mono g _ _ ih
    · exact le_rfl

end PEqualNP.Outside.L_meta_1315

theorem PEqualNP.Outside.L_meta_1315 :
∀ (n : ℕ) (marked marked2 : Finset ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (D : ℕ), PEqualNP.MetaComplexity.Monotone2 C → marked ⊆ marked2 → PEqualNP.CircuitLowerBounds.HasLineDegree n marked2 C D → PEqualNP.CircuitLowerBounds.HasLineDegree n marked C D := by
  open PEqualNP.Outside.L_meta_1315 PEqualNP.CircuitLowerBounds in
  intro n marked marked2 C D _ hsub hD
  obtain ⟨gs, o⟩ := C
  exact le_trans (ld_mono gs o n marked marked2 hsub o) hD
