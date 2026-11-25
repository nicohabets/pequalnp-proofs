import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1277

/-! The wire list is the input degrees followed by the AND gate, whose degree is the sum of the degrees of the point input p (unmarked, 0) and the line input P + w (marked, 1). The output index P + L is that gate. -/

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

end PEqualNP.Outside.L_meta_1277

theorem PEqualNP.Outside.L_meta_1277 :
∀ (P L : ℕ) (p : Fin P) (w : Fin L), ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [p.val, P + w.val]⟩], output := P + L } : PEqualNP.CircuitLowerBounds.Circuit).lineDeg (P + L) (Finset.Ico P (P + L)) = 1 := by
  open PEqualNP.Outside.L_meta_1277 PEqualNP.CircuitLowerBounds in
  intro P L p w
  have h := ld_snoc [] ⟨GateOp.and, [p.val, P + w.val]⟩ (P + L) (P + L) (P + L) (Finset.Ico P (P + L))
  simp only [List.nil_append] at h
  rw [Circuit.lineDeg]
  dsimp only
  rw [h, getD_snoc, ld_length, if_neg (by simp), if_pos (by simp)]
  have hp := p.isLt
  have hw := w.isLt
  have hp' : (p : ℕ) < P + L := by omega
  have hw' : P + (w : ℕ) < P + L := by omega
  simp [Gate.lineDegree, Circuit.lineDegrees, List.getD_eq_getElem?_getD, List.getElem?_range hp',
    List.getElem?_range hw']
