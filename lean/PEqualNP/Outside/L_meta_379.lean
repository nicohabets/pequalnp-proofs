import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_379

/-! The code is the concatenation of the codes of its items: a literal item is coded by
`encodeLiteral`, a clause end by `[false, false]`. Reading one item (`headI`) returns exactly
the code of the first item and `dropI` removes it; this is induction on the binary digits of
the literal. Hence the `i`-th iterate of `dropI` starts at item `i`, its first item starts with
`[false, false]` exactly when item `i` is a clause end, and the count follows by induction on
`j`. -/

open PEqualNP.Search

/-- The code of one item: a literal, or the end of a clause. -/
def code (o : Option Literal) : List Bool :=
  match o with
  | some l => encodeLiteral l
  | none => [false, false]

theorem enc_eq (φ : CNF) :
    encodeCNF φ = (φ.flatMap fun c => c.map some ++ [none]).flatMap code := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [encodeCNF, encodeClause, List.flatMap_cons, List.flatMap_append] at ih ⊢
    rw [ih]
    simp [code, List.flatMap_map]

section
variable (headI dropI : List Bool → List Bool)
  (h2 : ∀ (d : Bool) (r : List Bool), headI (true :: d :: r) = true :: d :: headI r)
  (h3 : ∀ (d : Bool) (r : List Bool), headI (false :: d :: r) = [false, d])
  (d2 : ∀ (d : Bool) (r : List Bool), dropI (true :: d :: r) = dropI r)
  (d3 : ∀ (d : Bool) (r : List Bool), dropI (false :: d :: r) = r)

include h2 h3 in
theorem head_digits (ds r : List Bool) :
    headI ((ds.flatMap fun d => [true, d]) ++ [false, true] ++ r) =
      (ds.flatMap fun d => [true, d]) ++ [false, true] := by
  induction ds with
  | nil => simpa using h3 true r
  | cons d ds ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
    rw [h2, ih]

include d2 d3 in
theorem drop_digits (ds r : List Bool) :
    dropI ((ds.flatMap fun d => [true, d]) ++ [false, true] ++ r) = r := by
  induction ds with
  | nil => simpa using d3 true r
  | cons d ds ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
    rw [d2, ih]

include h2 h3 in
theorem head_code (o : Option Literal) (r : List Bool) : headI (code o ++ r) = code o := by
  cases o with
  | none => simpa [code] using h3 false r
  | some l =>
    have := head_digits headI h2 h3 l.1.bits r
    simp only [code, encodeLiteral, List.cons_append, List.nil_append, List.append_assoc] at this ⊢
    rw [h2, this]

include d2 d3 in
theorem drop_code (o : Option Literal) (r : List Bool) : dropI (code o ++ r) = r := by
  cases o with
  | none => simpa [code] using d3 false r
  | some l =>
    have := drop_digits dropI d2 d3 l.1.bits r
    simp only [code, encodeLiteral, List.cons_append, List.nil_append, List.append_assoc] at this ⊢
    rw [d2, this]

include d2 d3 in
theorem iter_drop (L : List (Option Literal)) (i : ℕ) (hi : i ≤ L.length) :
    dropI^[i] (L.flatMap code) = (L.drop i).flatMap code := by
  induction i generalizing L with
  | zero => simp
  | succ i ih =>
    cases L with
    | nil => simp at hi
    | cons o L =>
      rw [Function.iterate_succ_apply, List.flatMap_cons, drop_code dropI d2 d3,
        ih L (by simp at hi; omega)]
      simp
end

theorem take2_code (o : Option Literal) :
    (code o).take 2 = [false, false] ↔ o = none := by
  cases o with
  | none => simp [code]
  | some l => simp [code, encodeLiteral]

theorem count_none (L : List (Option Literal)) (j : ℕ) (hj : j ≤ L.length) :
    (List.range j).countP (fun i => decide (L[i]? = some none)) = (L.take j).count none := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j < L.length := by omega
    rw [List.range_succ, List.countP_append, ih (by omega), List.take_add_one,
      List.getElem?_eq_getElem hj', List.count_append]
    by_cases h : L[j] = none <;> simp [h, List.getElem?_eq_getElem hj']

end PEqualNP.Outside.L_meta_379

theorem PEqualNP.Outside.L_meta_379 :
∀ (headI dropI : List Bool → List Bool), headI [] = [] → (∀ a : Bool, headI [a] = [a]) → (∀ (d : Bool) (r : List Bool), headI (true :: d :: r) = true :: d :: headI r) → (∀ (d : Bool) (r : List Bool), headI (false :: d :: r) = [false, d]) → dropI [] = [] → (∀ a : Bool, dropI [a] = []) → (∀ (d : Bool) (r : List Bool), dropI (true :: d :: r) = dropI r) → (∀ (d : Bool) (r : List Bool), dropI (false :: d :: r) = r) → ∀ (φ : PEqualNP.Search.CNF) (j : ℕ), j ≤ (φ.flatMap (fun c => c.map some ++ [none])).length → (List.range j).countP (fun i => decide ((headI (dropI^[i] (PEqualNP.Search.encodeCNF φ))).take 2 = [false, false])) = ((φ.flatMap (fun c => c.map some ++ [none])).take j).count none
 := by
  open PEqualNP.Outside.L_meta_379 PEqualNP.Search in
  intro headI dropI _ _ h2 h3 _ _ d2 d3 φ j hj
  rw [enc_eq]
  generalize (φ.flatMap fun c => c.map some ++ [none]) = L at hj ⊢
  rw [← count_none L j hj]
  apply List.countP_congr
  intro i hi
  have hi' : i < L.length := by simp at hi; omega
  rw [iter_drop dropI d2 d3 L i (by omega), List.drop_eq_getElem_cons hi', List.flatMap_cons,
    head_code headI h2 h3]
  simp only [decide_eq_true_eq, take2_code, List.getElem?_eq_getElem hi']
  simp
