import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_490

/-! Split the formula as the first `i` clauses, clause `i`, and the rest. The items of the first
`i` clauses number exactly `off i` (each clause gives its literals and one end marker), so item
`off i + k` is item `k` of clause `i`'s items followed by the rest: its literal `k` for
`k < |c_i|`, and its end marker for `k = |c_i|`. -/

end PEqualNP.Outside.L_meta_490

theorem PEqualNP.Outside.L_meta_490 :
∀ (φ : PEqualNP.Search.CNF) (off : ℕ → ℕ), (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → ∀ i < φ.length, (∀ j < (φ.getD i []).length, (φ.flatMap (fun c => c.map some ++ [none]))[off i + j]? = some (some ((φ.getD i []).getD j (0, false)))) ∧ (φ.flatMap (fun c => c.map some ++ [none]))[off i + (φ.getD i []).length]? = some none := by
  intro φ off hoff i hi
  have hsplit : φ = φ.take i ++ φ[i] :: φ.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hlen : ((φ.take i).flatMap (fun c => c.map some ++ [none])).length = off i := by
    rw [hoff, List.length_flatMap]
    simp
  have hgd : φ.getD i [] = φ[i] := by simp [List.getD_eq_getElem?_getD, hi]
  have key : ∀ k, (φ.flatMap (fun c => c.map some ++ [none]))[off i + k]? =
      (φ[i].map some ++ [none] ++ (φ.drop (i + 1)).flatMap (fun c => c.map some ++ [none]))[k]? := by
    intro k
    conv_lhs => rw [hsplit]
    rw [List.flatMap_append, List.flatMap_cons, List.getElem?_append_right (by rw [hlen]; omega),
      hlen, Nat.add_sub_cancel_left]
  rw [hgd]
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [key, List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, hj]
  · rw [key, List.getElem?_append_left (by simp), List.getElem?_append_right (by simp)]
    simp
