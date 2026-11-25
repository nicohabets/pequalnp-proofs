import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8429
open PEqualNP.CircuitLowerBounds



theorem other {n : ℕ} (v : Fin n) (e : Sym2 (Fin n)) (hv : v ∈ e) (hnd : ¬ e.IsDiag) :
    ∃ u, u ≠ v ∧ e = s(v, u) := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff] at hnd
    rcases Sym2.mem_iff.1 hv with h | h
    · subst h
      exact ⟨b, fun h => hnd h.symm, rfl⟩
    · subst h
      exact ⟨a, hnd, Sym2.eq_swap⟩

theorem mapv {n : ℕ} (c : Fin n → Bool) (v u : Fin n) (b : Bool) (hu : u ≠ v) :
    Sym2.map (Function.update c v b) s(v, u) = s(b, c u) := by
  show s(Function.update c v b v, Function.update c v b u) = _
  rw [Function.update_self, Function.update_of_ne hu]

theorem flipcut {n : ℕ} (c : Fin n → Bool) (v : Fin n) (e : Sym2 (Fin n)) (hv : v ∈ e)
    (hnd : ¬ e.IsDiag) :
    ¬(Sym2.map (Function.update c v true) e).IsDiag ∨
    ¬(Sym2.map (Function.update c v false) e).IsDiag := by
  obtain ⟨u, hu, rfl⟩ := other v e hv hnd
  cases hcu : c u
  · left
    rw [mapv c v u true hu, Sym2.mk_isDiag_iff, hcu]
    decide
  · right
    rw [mapv c v u false hu, Sym2.mk_isDiag_iff, hcu]
    decide

theorem flip_iff {n : ℕ} (c : Fin n → Bool) (v : Fin n) (e : Sym2 (Fin n)) (hv : v ∈ e)
    (hnd : ¬ e.IsDiag) :
    (Sym2.map (Function.update c v (!c v)) e).IsDiag ↔ ¬(Sym2.map c e).IsDiag := by
  obtain ⟨u, hu, rfl⟩ := other v e hv hnd
  rw [mapv c v u (!c v) hu, show Sym2.map c s(v, u) = s(c v, c u) from rfl, Sym2.mk_isDiag_iff,
    Sym2.mk_isDiag_iff]
  cases c v <;> cases c u <;> simp

theorem split_card {α : Type} [DecidableEq α] (S : Finset α) (p : α → Prop) [DecidablePred p] :
    S.card = (S.filter p).card + (S.filter fun x => ¬p x).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  · rw [Finset.disjoint_left]
    intro x h1 h2
    exact (Finset.mem_filter.1 h2).2 (Finset.mem_filter.1 h1).2

theorem halfcut {n : ℕ} (E : Finset (Sym2 (Fin n))) (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    ∀ V : Finset (Fin n), ∃ c : Fin n → Bool,
      (E.filter fun e => ∀ x ∈ e, x ∈ V).card
        ≤ 2 * ((E.filter fun e => ∀ x ∈ e, x ∈ V).filter fun e => ¬(Sym2.map c e).IsDiag).card := by
  classical
  intro V
  induction V using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => false, ?_⟩
    have h0 : (E.filter fun e => ∀ x ∈ e, x ∈ (∅ : Finset (Fin n))) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro e _ h
      induction e using Sym2.ind with
      | _ a b => exact absurd (h a (Sym2.mem_mk_left a b)) (Finset.notMem_empty a)
    rw [h0]
    simp
  | insert v V hv ih =>
    obtain ⟨c, hc⟩ := ih
    have hsplit : (E.filter fun e => ∀ x ∈ e, x ∈ insert v V)
        = (E.filter fun e => ∀ x ∈ e, x ∈ V) ∪
          (E.filter fun e => v ∈ e ∧ ∀ x ∈ e, x ∈ insert v V) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨heE, hall⟩
        by_cases hve : v ∈ e
        · exact Or.inr ⟨heE, hve, hall⟩
        · refine Or.inl ⟨heE, fun x hx => ?_⟩
          rcases Finset.mem_insert.1 (hall x hx) with h | h
          · exact absurd (h ▸ hx) hve
          · exact h
      · rintro (⟨heE, hall⟩ | ⟨heE, _, hall⟩)
        · exact ⟨heE, fun x hx => Finset.mem_insert_of_mem (hall x hx)⟩
        · exact ⟨heE, hall⟩
    have hdis : Disjoint (E.filter fun e => ∀ x ∈ e, x ∈ V)
        (E.filter fun e => v ∈ e ∧ ∀ x ∈ e, x ∈ insert v V) := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      exact hv ((Finset.mem_filter.1 h1).2 v (Finset.mem_filter.1 h2).2.1)
    have hcard := Finset.card_union_of_disjoint hdis
    have hcover : (E.filter fun e => v ∈ e ∧ ∀ x ∈ e, x ∈ insert v V)
        ⊆ ((E.filter fun e => v ∈ e ∧ ∀ x ∈ e, x ∈ insert v V).filter
            fun e => ¬(Sym2.map (Function.update c v true) e).IsDiag) ∪
          ((E.filter fun e => v ∈ e ∧ ∀ x ∈ e, x ∈ insert v V).filter
            fun e => ¬(Sym2.map (Function.update c v false) e).IsDiag) := by
      intro e he
      obtain ⟨heE, hve, _⟩ := Finset.mem_filter.1 he
      rcases flipcut c v e hve (hE e heE) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨he, h⟩)
    have hcov := le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
    have hlow : ∀ b : Bool,
        ((E.filter fun e => ∀ x ∈ e, x ∈ V).filter fun e => ¬(Sym2.map c e).IsDiag).card
          + ((E.filter fun e => v ∈ e ∧ ∀ x ∈ e, x ∈ insert v V).filter
              fun e => ¬(Sym2.map (Function.update c v b) e).IsDiag).card
        ≤ ((E.filter fun e => ∀ x ∈ e, x ∈ insert v V).filter
              fun e => ¬(Sym2.map (Function.update c v b) e).IsDiag).card := by
      intro b
      rw [← Finset.card_union_of_disjoint]
      · apply Finset.card_le_card
        intro e he
        rcases Finset.mem_union.1 he with h | h
        · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h
          refine Finset.mem_filter.2 ⟨by rw [hsplit]; exact Finset.mem_union_left _ h1, ?_⟩
          have hmap : Sym2.map (Function.update c v b) e = Sym2.map c e := by
            apply Sym2.map_congr
            intro x hx
            have hxv : x ≠ v := fun h => hv (h ▸ (Finset.mem_filter.1 h1).2 x hx)
            exact Function.update_of_ne hxv b c
          rw [hmap]
          exact h2
        · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h
          exact Finset.mem_filter.2 ⟨by rw [hsplit]; exact Finset.mem_union_right _ h1, h2⟩
      · rw [Finset.disjoint_left]
        intro e h1 h2
        exact (Finset.disjoint_left.1 hdis) (Finset.mem_filter.1 h1).1 (Finset.mem_filter.1 h2).1
    have ht := hlow true
    have hf := hlow false
    rw [hsplit, hcard]
    rw [hsplit] at ht hf
    by_cases hbig : ((E.filter fun e => v ∈ e ∧ ∀ x ∈ e, x ∈ insert v V).filter
        fun e => ¬(Sym2.map (Function.update c v false) e).IsDiag).card
        ≤ ((E.filter fun e => v ∈ e ∧ ∀ x ∈ e, x ∈ insert v V).filter
        fun e => ¬(Sym2.map (Function.update c v true) e).IsDiag).card
    · exact ⟨Function.update c v true, by omega⟩
    · exact ⟨Function.update c v false, by omega⟩

end PEqualNP.Outside.L_meta_8429

open PEqualNP.Outside.L_meta_8429 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8429 : ∀ (x1 : ℕ) (x2 : Finset (Sym2 (Fin x1))), (∀ (x3 : Fin x1), s(x3, x3) ∉ x2) → ∃ (x4 : Finset (Sym2 (Fin x1))) (x5 : Fin x1 → Bool), x4 ⊆ x2 ∧ (∀ (x6 x7 : Fin x1), s(x6, x7) ∈ x4 → x5 x6 ≠ x5 x7) ∧ x2.card ≤ (2 : ℕ) * x4.card ∧ ∀ (x6 : Fin x1), {x7 ∈ x2 | x6 ∈ x7}.card ≤ (2 : ℕ) * {x7 ∈ x4 | x6 ∈ x7}.card := by
  intro n E hE0
  classical
  have hE : ∀ e ∈ E, ¬ e.IsDiag := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [Sym2.mk_isDiag_iff]
      intro hab
      subst hab
      exact hE0 a he
  obtain ⟨c, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n → Bool))
    (fun c => (E.filter fun e => ¬(Sym2.map c e).IsDiag).card) ⟨fun _ => false, Finset.mem_univ _⟩
  refine ⟨E.filter fun e => ¬(Sym2.map c e).IsDiag, c, Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 := (Finset.mem_filter.1 hab).2
    rw [show Sym2.map c s(a, b) = s(c a, c b) from rfl, Sym2.mk_isDiag_iff] at h1
    exact h1
  · obtain ⟨c0, hc0⟩ := halfcut E hE Finset.univ
    have hall : (E.filter fun e => ∀ x ∈ e, x ∈ (Finset.univ : Finset (Fin n))) = E := by
      apply Finset.filter_true_of_mem
      intro e _ x _
      exact Finset.mem_univ x
    rw [hall] at hc0
    have h2 := hmax c0 (Finset.mem_univ _)
    omega
  · intro v
    have hm := hmax (Function.update c v (!c v)) (Finset.mem_univ _)
    have hsub : ((E.filter fun e => ¬(Sym2.map c e).IsDiag).filter fun e => ¬ v ∈ e) ∪
        ((E.filter fun e => v ∈ e).filter fun e => ¬¬(Sym2.map c e).IsDiag)
        ⊆ E.filter fun e => ¬(Sym2.map (Function.update c v (!c v)) e).IsDiag := by
      intro e he
      rcases Finset.mem_union.1 he with h | h
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h
        obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
        refine Finset.mem_filter.2 ⟨h3, ?_⟩
        have hmap : Sym2.map (Function.update c v (!c v)) e = Sym2.map c e := by
          apply Sym2.map_congr
          intro x hx
          have hxv : x ≠ v := by
            intro h6
            rw [h6] at hx
            exact h2 hx
          exact Function.update_of_ne hxv _ c
        rw [hmap]
        exact h4
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h
        obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
        refine Finset.mem_filter.2 ⟨h3, ?_⟩
        rw [flip_iff c v e h4 (hE e h3)]
        exact h2
    have hdis : Disjoint ((E.filter fun e => ¬(Sym2.map c e).IsDiag).filter fun e => ¬ v ∈ e)
        ((E.filter fun e => v ∈ e).filter fun e => ¬¬(Sym2.map c e).IsDiag) := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      exact (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 (Finset.mem_filter.1 h2).1).2
    have h5 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis] at h5
    have s1 := split_card (E.filter fun e => ¬(Sym2.map c e).IsDiag) (fun e => v ∈ e)
    have s2 := split_card (E.filter fun e => v ∈ e) (fun e => ¬(Sym2.map c e).IsDiag)
    have heq : ((E.filter fun e => v ∈ e).filter fun e => ¬(Sym2.map c e).IsDiag)
        = ((E.filter fun e => ¬(Sym2.map c e).IsDiag).filter fun e => v ∈ e) := by
      ext e
      simp only [Finset.mem_filter]
      tauto
    rw [heq] at s2
    omega
