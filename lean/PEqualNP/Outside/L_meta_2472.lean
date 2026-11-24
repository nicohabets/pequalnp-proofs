import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2472
open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

def Rel (A B : List (List ℕ)) : Prop :=
  ∀ v ∈ A, ∃ v' ∈ B, v = v'.map (fun a => min a 2)

theorem mem_insertNew (A : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew A v ↔ x ∈ A ∨ x = v := by
  unfold insertNew
  split
  · constructor
    · intro h; exact Or.inl h
    · rintro (h | rfl)
      · exact h
      · assumption
  · simp

theorem mem_fold (A : List (List ℕ)) : ∀ (acc : List (List ℕ)) (x : List ℕ),
    x ∈ A.foldl insertNew acc ↔ x ∈ acc ∨ x ∈ A := by
  induction A with
  | nil => intro acc x; simp
  | cons a t ih =>
    intro acc x
    rw [List.foldl_cons, ih, mem_insertNew, List.mem_cons]
    tauto

theorem mem_orfold (ins : List (List (List ℕ))) : ∀ (acc : List (List ℕ)) (x : List ℕ),
    x ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc ↔ x ∈ acc ∨ ∃ A ∈ ins, x ∈ A := by
  induction ins with
  | nil => intro acc x; simp
  | cons a t ih =>
    intro acc x
    rw [List.foldl_cons, ih, mem_fold]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem mem_andStep (k : ℕ) (A B : List (List ℕ)) (x : List ℕ) :
    x ∈ andStep k A B ↔ ∃ u ∈ A, ∃ v ∈ B, capAdd k u v = x := by
  unfold andStep
  rw [mem_fold]
  simp [List.mem_flatMap]

theorem cap_map (u v : List ℕ) :
    capAdd 1 (u.map (fun a => min a 2)) (v.map (fun a => min a 2))
      = (capAdd 2 u v).map (fun a => min a 2) := by
  unfold capAdd
  rw [List.zipWith_map, List.map_zipWith]
  congr 1
  funext a b
  omega

theorem rel_and (A1 A2 B1 B2 : List (List ℕ)) (hA : Rel A1 A2) (hB : Rel B1 B2) :
    Rel (andStep 1 A1 B1) (andStep 2 A2 B2) := by
  intro x hx
  rw [mem_andStep] at hx
  obtain ⟨u, hu, v, hv, rfl⟩ := hx
  obtain ⟨u', hu', rfl⟩ := hA u hu
  obtain ⟨v', hv', rfl⟩ := hB v hv
  exact ⟨capAdd 2 u' v', (mem_andStep 2 A2 B2 _).2 ⟨u', hu', v', hv', rfl⟩, cap_map u' v'⟩

theorem rel_andfold (R1 R2 : List (List (List ℕ)))
    (h : ∀ i, Rel (R1.getD i []) (R2.getD i [])) (is : List ℕ) :
    ∀ acc1 acc2 : List (List ℕ), Rel acc1 acc2 →
      Rel ((is.map fun i => R1.getD i []).foldl (andStep 1) acc1)
        ((is.map fun i => R2.getD i []).foldl (andStep 2) acc2) := by
  induction is with
  | nil => intro a1 a2 ha; exact ha
  | cons i t ih =>
    intro a1 a2 ha
    simp only [List.map_cons, List.foldl_cons]
    exact ih _ _ (rel_and _ _ _ _ ha (h i))

theorem rel_orfold (R1 R2 : List (List (List ℕ)))
    (h : ∀ i, Rel (R1.getD i []) (R2.getD i [])) (is : List ℕ) :
    Rel ((is.map fun i => R1.getD i []).foldl (fun acc A => A.foldl insertNew acc) [])
      ((is.map fun i => R2.getD i []).foldl (fun acc A => A.foldl insertNew acc) []) := by
  intro x hx
  rw [mem_orfold] at hx
  rcases hx with hx | ⟨A, hA, hx⟩
  · simp at hx
  · rw [List.mem_map] at hA
    obtain ⟨i, hi, rfl⟩ := hA
    obtain ⟨x', hx', e⟩ := h i x hx
    exact ⟨x', (mem_orfold _ _ _).2 (Or.inr ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, hx'⟩), e⟩

theorem rel_snoc (R1 R2 : List (List (List ℕ))) (a1 a2 : List (List ℕ))
    (hlen : R1.length = R2.length)
    (h : ∀ i, Rel (R1.getD i []) (R2.getD i [])) (ha : Rel a1 a2) :
    ∀ i, Rel ((R1 ++ [a1]).getD i []) ((R2 ++ [a2]).getD i []) := by
  intro i
  by_cases hi : i < R1.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hlen ▸ hi)]
    exact h i
  · have hi' : R1.length ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ hi', List.getD_append_right _ _ _ _ (hlen ▸ hi'), ← hlen]
    rcases Nat.eq_zero_or_pos (i - R1.length) with h0 | h0
    · rw [h0]; exact ha
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i - R1.length ≠ 0)
      rw [hm]
      intro v hv
      simp at hv

theorem main (gs : List Gate) : ∀ (R1 R2 : List (List (List ℕ))),
    R1.length = R2.length → (∀ i, Rel (R1.getD i []) (R2.getD i [])) →
    ∀ i, Rel
      ((gs.foldl (fun R g =>
        let ins := g.inputs.map fun i => R.getD i []
        R ++ [match g.op with
          | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
          | GateOp.and => ins.foldl (andStep 1) [[0, 0]]
          | _ => []]) R1).getD i [])
      ((gs.foldl (fun R g =>
        let ins := g.inputs.map fun i => R.getD i []
        R ++ [match g.op with
          | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
          | GateOp.and => ins.foldl (andStep 2) [[0, 0]]
          | _ => []]) R2).getD i []) := by
  induction gs with
  | nil => intro R1 R2 _ h; exact h
  | cons g t ih =>
    intro R1 R2 hlen h
    simp only [List.foldl_cons]
    apply ih
    · simp [hlen]
    · apply rel_snoc _ _ _ _ hlen h
      rcases g with ⟨op, inputs⟩
      cases op
      · exact rel_andfold R1 R2 h inputs _ _ (by
          intro v hv
          exact ⟨v, hv, by simp at hv; subst hv; rfl⟩)
      · exact rel_orfold R1 R2 h inputs
      · intro v hv; simp at hv
      · intro v hv; simp at hv
      · intro v hv; simp at hv

theorem leaf (n u w : ℕ) : ∀ i,
    Rel (((List.range n).map (leafVectors [u, w] 1)).getD i [])
      (((List.range n).map (leafVectors [u, w] 2)).getD i []) := by
  intro i
  by_cases hi : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
    intro v hv
    refine ⟨v, ?_, ?_⟩
    · simpa [leafVectors] using hv
    · unfold leafVectors at hv
      split at hv
      · simp only [List.mem_singleton] at hv
        subst hv
        simp only [List.map_cons, List.map_nil]
        split <;> split <;> simp
      · simp at hv
  · intro v hv
    simp [List.getD_eq_getElem?_getD, hi] at hv

theorem getD_le (l : List ℕ) (H : ∀ a ∈ l, a ≤ 1) (j : ℕ) : l.getD j 0 ≤ 1 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[j]? with
  | none => simp
  | some a => simpa using H a (List.mem_of_getElem? h)

end PEqualNP.Outside.L_meta_2472

theorem PEqualNP.Outside.L_meta_2472 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.ReadK.readsAtMost C n [u, w] 1 = true → ((PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output []).any (fun v_1 => decide (v_1.getD 0 0 ≤ 1 ∧ v_1.getD 1 0 ≤ 1)) = true := by
  intro n C u w h
  unfold PEqualNP.ReadK.readsAtMost at h
  rw [List.any_eq_true] at h
  obtain ⟨v, hv, hall⟩ := h
  have hm := PEqualNP.Outside.L_meta_2472.main C.gates _ _ (by simp)
    (PEqualNP.Outside.L_meta_2472.leaf n u w) C.output
  obtain ⟨v', hv', e⟩ := hm v hv
  rw [List.any_eq_true]
  refine ⟨v', hv', ?_⟩
  have H : ∀ a ∈ v', a ≤ 1 := by
    intro a ha
    rw [List.all_eq_true] at hall
    have := hall (min a 2) (by rw [e]; exact List.mem_map.2 ⟨a, ha, rfl⟩)
    simp at this
    omega
  simp only [decide_eq_true_eq]
  exact ⟨PEqualNP.Outside.L_meta_2472.getD_le v' H 0, PEqualNP.Outside.L_meta_2472.getD_le v' H 1⟩
