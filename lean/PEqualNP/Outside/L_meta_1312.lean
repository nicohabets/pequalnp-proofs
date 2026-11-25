import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1312

/-! By induction along the gates, every entry of the degree list is at most 1: input degrees are 0 or 1, and an OR gate takes a maximum of entries read from the list (a missing wire counts 0), which is at most 1. The output degree is one of the entries or 0. -/

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

theorem getD_le (l : List ℕ) (B i : ℕ) (h : ∀ x ∈ l, x ≤ B) : l.getD i 0 ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[i]? with
  | none => simp
  | some x =>
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hx
    simpa using h _ (List.getElem_mem hi)

theorem foldr_max_le (l : List ℕ) (B : ℕ) (h : ∀ x ∈ l, x ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem all_le_one (gs : List Gate) (o n : ℕ) (marked : Finset ℕ)
    (hor : ∀ g ∈ gs, g.op = GateOp.or) : ∀ x ∈ Circuit.lineDegrees ⟨gs, o⟩ n marked, x ≤ 1 := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro x hx
    simp only [Circuit.lineDegrees, List.foldl_nil, List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    split_ifs <;> simp
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hor g' (by simp [hg']))
    rw [ld_snoc _ _ _ o]
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact ih' x hx
    · simp only [List.mem_singleton] at hx
      subst hx
      have hg : g.op = GateOp.or := hor g (by simp)
      unfold Gate.lineDegree
      rw [if_neg (by rw [hg]; simp)]
      apply foldr_max_le
      intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨i, _, rfl⟩ := hy
      exact getD_le _ _ _ ih'

end PEqualNP.Outside.L_meta_1312

theorem PEqualNP.Outside.L_meta_1312 :
∀ (n : ℕ) (marked : Finset ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.CircuitLowerBounds.HasLineDegree n marked C 1 := by
  open PEqualNP.Outside.L_meta_1312 PEqualNP.CircuitLowerBounds in
  intro n marked C hor
  obtain ⟨gs, o⟩ := C
  exact getD_le _ _ _ (all_le_one gs o n marked hor)
