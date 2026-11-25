import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9089

-- listLe, gate_mono and wires_mono are copied from the merged L-meta-10173 by domvil.

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

def listLe (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false = true → y.getD i false = true

theorem gate_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (w1 w2 : List Bool) (hle : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    op.eval (l.map fun i => w1.getD i false) = true →
      op.eval (l.map fun i => w2.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro h b hb
    rcases hb with ⟨i, hi, rfl⟩
    exact hle i (h (w1.getD i false) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, h1⟩
    exact ⟨w2.getD i false, ⟨i, hi, rfl⟩, hle i h1⟩

theorem wires_mono (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w1 w2 : List Bool) (hle : listLe w1 w2) :
    listLe (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1)
           (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2) := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg := hm g List.mem_cons_self
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
    apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp [hle.1], fun i hi => ?_⟩
    simp only [List.getD_eq_getElem?_getD] at hi ⊢
    by_cases hlt : i < w1.length
    · have hlt2 : i < w2.length := by rw [← hle.1]; exact hlt
      rw [List.getElem?_append_left hlt] at hi
      rw [List.getElem?_append_left hlt2]
      exact hle.2 i (by simpa [List.getD_eq_getElem?_getD] using hi)
    · by_cases heq : i = w1.length
      · subst heq
        rw [List.getElem?_append_right (le_refl _), Nat.sub_self] at hi
        rw [hle.1, List.getElem?_append_right (le_refl _), Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.getD_some] at hi ⊢
        exact gate_mono g.op hop g.inputs w1 w2 hle.2 hi
      · rw [List.getElem?_eq_none (by simp; omega)] at hi
        simp at hi

theorem input_le {n m : ℕ} (X X' : Finset (Fin n)) (Y Y' : Finset (Fin m))
    (hX : X ⊆ X') (hY : Y ⊆ Y') : listLe (incidenceInput X Y) (incidenceInput X' Y') := by
  refine ⟨by simp [incidenceInput], fun i hi => ?_⟩
  simp only [incidenceInput, List.getD_eq_getElem?_getD] at hi ⊢
  by_cases h1 : i < n
  · rw [List.getElem?_append_left (by simpa using h1)] at hi ⊢
    simp only [List.getElem?_ofFn, h1] at hi ⊢
    simp only [List.ofFnNthVal, h1, dite_true, Option.getD_some, decide_eq_true_eq] at hi ⊢
    exact hX hi
  · rw [List.getElem?_append_right (by simpa using h1)] at hi ⊢
    simp only [List.length_ofFn, List.getElem?_ofFn] at hi ⊢
    by_cases h2 : i - n < m
    · simp only [List.ofFnNthVal, h2, dite_true, Option.getD_some, decide_eq_true_eq] at hi ⊢
      exact hY hi
    · simp [List.ofFnNthVal, h2] at hi

theorem eval_mono {n m : ℕ} (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (X X' : Finset (Fin n)) (Y Y' : Finset (Fin m)) (hX : X ⊆ X') (hY : Y ⊆ Y')
    (h : C.eval (incidenceInput X Y) = true) : C.eval (incidenceInput X' Y') = true :=
  (wires_mono C.gates hm _ _ (input_le X X' Y Y' hX hY)).2 C.output h

theorem exists_max {n m : ℕ} (S : Fin m → Finset (Fin n)) :
    ∀ k : ℕ, ∀ (X : Finset (Fin n)) (Y : Finset (Fin m)),
      (Finset.univ \ X).card + (Finset.univ \ Y).card ≤ k → IsFalseInput S X Y →
      ∃ X' Y', X ⊆ X' ∧ Y ⊆ Y' ∧ IsMaximalFalse S X' Y' := by
  intro k
  induction k with
  | zero =>
    intro X Y hk hf
    refine ⟨X, Y, subset_rfl, subset_rfl, hf, fun p hp => ?_, fun l hl => ?_⟩
    · exfalso
      have : p ∈ Finset.univ \ X := by simp [hp]
      have := Finset.card_pos.mpr ⟨p, this⟩
      omega
    · exfalso
      have : l ∈ Finset.univ \ Y := by simp [hl]
      have := Finset.card_pos.mpr ⟨l, this⟩
      omega
  | succ k ih =>
    intro X Y hk hf
    by_cases hp : ∃ p, p ∉ X ∧ IsFalseInput S (insert p X) Y
    · obtain ⟨p, hpX, hf'⟩ := hp
      have hlt : (Finset.univ \ insert p X).card < (Finset.univ \ X).card := by
        apply Finset.card_lt_card
        refine ⟨Finset.sdiff_subset_sdiff subset_rfl (Finset.subset_insert _ _), fun hs => ?_⟩
        have : p ∈ Finset.univ \ X := by simp [hpX]
        have := hs this
        simp at this
      obtain ⟨X', Y', h1, h2, h3⟩ := ih (insert p X) Y (by omega) hf'
      exact ⟨X', Y', (Finset.subset_insert _ _).trans h1, h2, h3⟩
    · by_cases hl : ∃ l, l ∉ Y ∧ IsFalseInput S X (insert l Y)
      · obtain ⟨l, hlY, hf'⟩ := hl
        have hlt : (Finset.univ \ insert l Y).card < (Finset.univ \ Y).card := by
          apply Finset.card_lt_card
          refine ⟨Finset.sdiff_subset_sdiff subset_rfl (Finset.subset_insert _ _), fun hs => ?_⟩
          have : l ∈ Finset.univ \ Y := by simp [hlY]
          have := hs this
          simp at this
        obtain ⟨X', Y', h1, h2, h3⟩ := ih X (insert l Y) (by omega) hf'
        exact ⟨X', Y', h1, (Finset.subset_insert _ _).trans h2, h3⟩
      · push_neg at hp hl
        exact ⟨X, Y, subset_rfl, subset_rfl, hf, fun p h => hp p h, fun l h => hl l h⟩

theorem main (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) :
    (∀ (X : Finset (Fin n)) (Y : Finset (Fin m)),
      C.eval (incidenceInput X Y) = incidenceFun S X Y) ↔
    RightOnIncidentPairs S C ∧ ∀ (X : Finset (Fin n)) (Y : Finset (Fin m)),
      IsMaximalFalse S X Y → C.eval (incidenceInput X Y) = false := by
  constructor
  · intro h
    refine ⟨fun l p hp => ?_, fun X Y hmax => ?_⟩
    · rw [h]
      simp only [incidenceFun, decide_eq_true_eq]
      exact ⟨p, Finset.mem_singleton_self p, l, Finset.mem_singleton_self l, hp⟩
    · rw [h]
      simp only [incidenceFun, decide_eq_false_iff_not]
      rintro ⟨p, hpX, l, hlY, hpl⟩
      exact Finset.disjoint_left.mp (hmax.1 l hlY) hpl hpX
  · rintro ⟨hr, hf⟩ X Y
    by_cases hi : ∃ p ∈ X, ∃ l ∈ Y, p ∈ S l
    · have hv : incidenceFun S X Y = true := by simp only [incidenceFun, decide_eq_true_eq]; exact hi
      rw [hv]
      obtain ⟨p, hpX, l, hlY, hpl⟩ := hi
      exact eval_mono C hm {p} X {l} Y (Finset.singleton_subset_iff.mpr hpX)
        (Finset.singleton_subset_iff.mpr hlY) (hr l p hpl)
    · have hv : incidenceFun S X Y = false := by
        simp only [incidenceFun, decide_eq_false_iff_not]; exact hi
      rw [hv]
      have hfi : IsFalseInput S X Y := by
        intro l hlY
        rw [Finset.disjoint_left]
        intro p hpl hpX
        exact hi ⟨p, hpX, l, hlY, hpl⟩
      obtain ⟨X', Y', h1, h2, h3⟩ := exists_max S _ X Y le_rfl hfi
      have h4 := hf X' Y' h3
      cases he : C.eval (incidenceInput X Y)
      · rfl
      · have := eval_mono C hm X X' Y Y' h1 h2 he
        rw [h4] at this
        exact absurd this (by decide)

end PEqualNP.Outside.L_meta_9089

theorem PEqualNP.Outside.L_meta_9089 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → ((∀ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x2)), x4.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = PEqualNP.GenericRejection.incidenceFun x3 x6 x7) ↔ PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 ∧ ∀ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x2)), PEqualNP.GenericRejection.IsMaximalFalse x3 x6 x7 → x4.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = Bool.false) :=
  fun n m S C hm => PEqualNP.Outside.L_meta_9089.main n m S C hm
