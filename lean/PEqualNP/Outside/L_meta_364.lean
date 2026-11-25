import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_364

/-! The code is the concatenation of the codes of its items: a literal item is coded by
`encodeLiteral`, a clause end by `[false, false]`. Reading one item (`headI`) returns exactly
the code of the first item and `dropI` removes it; this is induction on the binary digits of
the literal. Hence the `j`-th iterate of `dropI` starts at item `j`; past the last item it is
the empty list, fixed by `dropI`, where `headI` gives the empty list. -/

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

end PEqualNP.Outside.L_meta_364

theorem PEqualNP.Outside.L_meta_364 :
∀ (headI dropI : List Bool → List Bool), headI [] = [] → (∀ a : Bool, headI [a] = [a]) → (∀ (d : Bool) (r : List Bool), headI (true :: d :: r) = true :: d :: headI r) → (∀ (d : Bool) (r : List Bool), headI (false :: d :: r) = [false, d]) → dropI [] = [] → (∀ a : Bool, dropI [a] = []) → (∀ (d : Bool) (r : List Bool), dropI (true :: d :: r) = dropI r) → (∀ (d : Bool) (r : List Bool), dropI (false :: d :: r) = r) → ∀ (φ : PEqualNP.Search.CNF) (j : ℕ), headI (dropI^[j] (PEqualNP.Search.encodeCNF φ)) = ((φ.flatMap (fun c => c.map some ++ [none]))[j]?).elim [] (fun o => o.elim [false, false] PEqualNP.Search.encodeLiteral) := by
  open PEqualNP.Outside.L_meta_364 PEqualNP.Search in
  intro headI dropI h0 _ h2 h3 d0 _ d2 d3 φ j
  rw [enc_eq]
  generalize (φ.flatMap fun c => c.map some ++ [none]) = L
  have hc : ∀ o : Option Literal, o.elim [false, false] encodeLiteral = code o := by
    intro o; cases o <;> rfl
  by_cases hj : j < L.length
  · rw [iter_drop dropI d2 d3 L j (by omega), List.drop_eq_getElem_cons hj, List.flatMap_cons,
      head_code headI h2 h3, List.getElem?_eq_getElem hj, Option.elim, hc]
  · have hk : j = (j - L.length) + L.length := by omega
    rw [hk, Function.iterate_add_apply, iter_drop dropI d2 d3 L L.length le_rfl,
      List.drop_length, List.flatMap_nil, Function.iterate_fixed d0, h0,
      List.getElem?_eq_none (by omega)]
    rfl
