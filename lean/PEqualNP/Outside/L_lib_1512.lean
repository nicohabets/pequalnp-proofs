import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1512

open Finset

theorem cut_eq {n : Nat} (cap : Fin n → Fin n → Nat) (Z : Finset (Fin n)) :
    Z.sum (fun a => (Finset.univ \ Z).sum (cap a))
      = ∑ a, ∑ b, (if a ∈ Z ∧ b ∉ Z then cap a b else 0) := by
  have h1 : ∑ a, ∑ b, (if a ∈ Z ∧ b ∉ Z then cap a b else 0)
      = ∑ a, (if a ∈ Z then ∑ b, (if b ∉ Z then cap a b else 0) else 0) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases ha : a ∈ Z <;> simp [ha]
  rw [h1, Finset.sum_ite_mem univ Z, Finset.univ_inter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_filter, Finset.sdiff_eq_filter]

theorem cut_sub {n : Nat} (cap : Fin n → Fin n → Nat) (X Y : Finset (Fin n)) :
    (X ∩ Y).sum (fun a => (Finset.univ \ (X ∩ Y)).sum (cap a))
      + (X ∪ Y).sum (fun a => (Finset.univ \ (X ∪ Y)).sum (cap a))
    ≤ X.sum (fun a => (Finset.univ \ X).sum (cap a))
      + Y.sum (fun a => (Finset.univ \ Y).sum (cap a)) := by
  rw [cut_eq, cut_eq, cut_eq, cut_eq, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun a _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun b _ => ?_)
  simp only [Finset.mem_inter, Finset.mem_union]
  by_cases h1 : a ∈ X <;> by_cases h2 : a ∈ Y <;> by_cases h3 : b ∈ X <;>
    by_cases h4 : b ∈ Y <;> simp [h1, h2, h3, h4]

theorem drop {α : Type} [DecidableEq α] (f : Finset α → Nat)
    (hsub : ∀ X Y, f (X ∩ Y) + f (X ∪ Y) ≤ f X + f Y) (L U : Finset α) (r : Nat) :
    ∀ (k : Nat) (I : Finset α), I.card = k → (∀ X, L ∪ I ⊆ X → X ⊆ U → r < f X) →
      ∃ J, J ⊆ I ∧ J.card ≤ r + 1 ∧ ∀ X, L ∪ J ⊆ X → X ⊆ U → r < f X := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro I hk hI
  by_cases hc : I.card ≤ r + 1
  · exact ⟨I, subset_refl _, hc, hI⟩
  have hex : ∃ v ∈ I, ∀ X, L ∪ I.erase v ⊆ X → X ⊆ U → r < f X := by
    by_contra hno
    push Not at hno
    have claim : ∀ S : Finset α, S ⊆ I → S.Nonempty →
        ∃ Y, L ∪ (I \ S) ⊆ Y ∧ Y ⊆ U ∧ f Y + S.card ≤ r + 1 := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _ h; exact absurd h (Finset.not_nonempty_empty)
      | insert v S hv ihS =>
        intro hS _
        have hvI : v ∈ I := hS (Finset.mem_insert_self v S)
        have hSI : S ⊆ I := fun x hx => hS (Finset.mem_insert_of_mem hx)
        obtain ⟨Xv, hXv1, hXv2, hXv3⟩ := hno v hvI
        rw [Finset.card_insert_of_notMem hv]
        by_cases hSe : S = ∅
        · subst hSe
          refine ⟨Xv, ?_, hXv2, by simp; omega⟩
          intro x hx
          apply hXv1
          simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
            Finset.notMem_empty, or_false, Finset.mem_erase] at hx ⊢
          tauto
        · obtain ⟨Y, hY1, hY2, hY3⟩ := ihS hSI (Finset.nonempty_iff_ne_empty.mpr hSe)
          have hU : L ∪ I ⊆ Y ∪ Xv := by
            intro x hx
            rcases Finset.mem_union.mp hx with h | h
            · exact Finset.mem_union_right _ (hXv1 (Finset.mem_union_left _ h))
            · by_cases hxv : x = v
              · subst hxv
                exact Finset.mem_union_left _
                  (hY1 (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, hv⟩)))
              · exact Finset.mem_union_right _
                  (hXv1 (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxv, h⟩)))
          have hr := hI (Y ∪ Xv) hU (Finset.union_subset hY2 hXv2)
          have hs := hsub Y Xv
          refine ⟨Y ∩ Xv, ?_, fun x hx => hY2 (Finset.mem_inter.mp hx).1, by omega⟩
          intro x hx
          rw [Finset.mem_inter]
          rcases Finset.mem_union.mp hx with h | h
          · exact ⟨hY1 (Finset.mem_union_left _ h), hXv1 (Finset.mem_union_left _ h)⟩
          · rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at h
            exact ⟨hY1 (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h.1, h.2.2⟩)),
              hXv1 (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h.2.1, h.1⟩))⟩
    obtain ⟨S, hSI, hSc⟩ := Finset.exists_subset_card_eq (s := I) (n := r + 2) (by omega)
    have hne : S.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨Y, _, _, hY⟩ := claim S hSI hne
    omega
  obtain ⟨v, hv, hP⟩ := hex
  have hlt : (I.erase v).card < k := by
    rw [Finset.card_erase_of_mem hv]; omega
  obtain ⟨J, hJ1, hJ2, hJ3⟩ := ih _ hlt (I.erase v) rfl hP
  exact ⟨J, hJ1.trans (Finset.erase_subset v I), hJ2, hJ3⟩

theorem main :
    ∀ (n r : Nat) (cap : Fin n → Fin n → Nat) (A B I O : Finset (Fin n)),
    let cut := fun (X : Finset (Fin n)) => X.sum (fun a => (Finset.univ \ X).sum (cap a))
    let fits := fun (J T X : Finset (Fin n)) => A ∪ J ⊆ X ∧ Disjoint (B ∪ T) X
    (∀ X, fits I O X → r<cut X) ↔
    ∃ J T : Finset (Fin n), J ⊆ I ∧ T ⊆ O ∧ J.card ≤ r+1 ∧ T.card ≤ r+1 ∧
      ∀ X, fits J T X → r<cut X := by
  intro n r cap A B I O cut fits
  constructor
  · intro h
    have hs : ∀ X Y, cut (X ∩ Y) + cut (X ∪ Y) ≤ cut X + cut Y := by
      intro X Y
      convert cut_sub cap X Y
    have hd : ∀ T X, Disjoint (B ∪ T) X ↔ X ⊆ (B ∪ T)ᶜ := fun T X =>
      Finset.subset_compl_iff_disjoint_left.symm
    obtain ⟨J, hJ1, hJ2, hJ3⟩ := drop cut hs A (B ∪ O)ᶜ r _ I rfl
      (fun X h1 h2 => h X ⟨h1, (hd O X).mpr h2⟩)
    have hs' : ∀ X Y, cut (X ∩ Y)ᶜ + cut (X ∪ Y)ᶜ ≤ cut Xᶜ + cut Yᶜ := by
      intro X Y
      rw [Finset.compl_inter, Finset.compl_union]
      have := hs Xᶜ Yᶜ
      omega
    obtain ⟨T, hT1, hT2, hT3⟩ := drop (fun Z => cut Zᶜ) hs' B (A ∪ J)ᶜ r _ O rfl
      (fun Z h1 h2 => hJ3 Zᶜ (Finset.subset_compl_comm.mp h2)
        (Finset.compl_subset_compl.mpr h1))
    refine ⟨J, T, hJ1, hT1, hJ2, hT2, fun X hX => ?_⟩
    have := hT3 Xᶜ (Finset.subset_compl_iff_disjoint_right.mpr hX.2)
      (Finset.compl_subset_compl.mpr hX.1)
    simpa using this
  · rintro ⟨J, T, hJ, hT, -, -, h⟩ X ⟨h1, h2⟩
    exact h X ⟨(Finset.union_subset_union (subset_refl A) hJ).trans h1,
      Finset.disjoint_of_subset_left (Finset.union_subset_union (subset_refl B) hT) h2⟩

end PEqualNP.Outside.L_lib_1512

open PEqualNP.Outside.L_lib_1512 in
theorem PEqualNP.Outside.L_lib_1512 :
    letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
    ∀ (n r : Nat) (cap : Fin n → Fin n → Nat) (A B I O : Finset (Fin n)),
    let cut := fun (X : Finset (Fin n)) => X.sum (fun a => (Finset.univ \ X).sum (cap a))
    let fits := fun (J T X : Finset (Fin n)) => A ∪ J ⊆ X ∧ Disjoint (B ∪ T) X
    (∀ X, fits I O X → r<cut X) ↔
    ∃ J T : Finset (Fin n), J ⊆ I ∧ T ⊆ O ∧ J.card ≤ r+1 ∧ T.card ≤ r+1 ∧
      ∀ X, fits J T X → r<cut X := by
  intro n r cap A B I O
  have h := main n r cap A B I O
  intro cut fits
  simp only [cut, fits]
  simp only at h
  convert h
