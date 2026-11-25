import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_779

/-! First bound: the ordered pairs of distinct points inside the sets are pairwise distinct
across the sets (two sets share at most one point), so `m d (d - 1) <= N (N - 1)`. Second
bound: with `r p` the number of sets through the point `p`, the sum of the `r p` is `m d` and
the sum of their squares is the sum over pairs of sets of the sizes of their intersections, at
most `m (d + m - 1)`; Cauchy-Schwarz gives `(m d)^2 <= N m (d + m - 1)`, and dividing by `m`
gives the claim. -/

end PEqualNP.Outside.L_meta_779

theorem PEqualNP.Outside.L_meta_779 :
∀ (N m d : ℕ) (S : Fin m → Finset (Fin N)),
  (∀ i : Fin m, (S i).card = d) →
  (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
  m * d * d + N ≤ N * N + m * d ∧ (1 ≤ m → m * d * d + N ≤ N * (m + d)) := by
  intro N m d S hd hS
  constructor
  · have hdisj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
        (fun i => (S i).offDiag) := by
      intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      rintro ⟨p, q⟩ h1 h2
      simp only [Finset.mem_offDiag] at h1 h2
      have hsub : ({p, q} : Finset (Fin N)) ⊆ S i ∩ S j := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.2 ⟨h1.1, h2.1⟩
        · exact Finset.mem_inter.2 ⟨h1.2.1, h2.2.1⟩
      have h3 := Finset.card_le_card hsub
      rw [Finset.card_pair h1.2.2] at h3
      have := hS i j hij
      omega
    have hsub : (Finset.univ.biUnion fun i => (S i).offDiag) ⊆
        (Finset.univ : Finset (Fin N)).offDiag := by
      intro x hx
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_offDiag] at hx ⊢
      obtain ⟨i, _, _, h3⟩ := hx
      exact h3
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdisj, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at h1
    simp only [Finset.offDiag_card, hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h1
    have hA := Nat.le_mul_self d
    have hB := Nat.le_mul_self N
    rw [Nat.mul_sub] at h1
    have hC : m * d ≤ m * (d * d) := Nat.mul_le_mul_left _ hA
    rw [mul_assoc]
    omega
  · intro hm
    have hr : ∀ p : Fin N, (Finset.univ.filter fun i => p ∈ S i).card =
        ∑ i, if p ∈ S i then 1 else 0 := fun p => Finset.card_filter _ _
    have hc : ∀ T : Finset (Fin N), (∑ p, if p ∈ T then 1 else 0) = T.card := by
      intro T
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hsum : ∑ p, (Finset.univ.filter fun i => p ∈ S i).card = m * d := by
      simp only [hr]
      rw [Finset.sum_comm]
      simp only [hc, hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hrow : ∀ i : Fin m, ∑ j, (S i ∩ S j).card ≤ d + (m - 1) := by
      intro i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Finset.inter_self, hd]
      have := Finset.sum_le_card_nsmul (Finset.univ.erase i) (fun j => (S i ∩ S j).card) 1
        (fun j hj => hS i j (Finset.ne_of_mem_erase hj).symm)
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one] at this
      omega
    have hsq : ∑ p, (Finset.univ.filter fun i => p ∈ S i).card ^ 2 ≤ m * (d + (m - 1)) := by
      have e : ∀ p : Fin N, (Finset.univ.filter fun i => p ∈ S i).card ^ 2 =
          ∑ i, ∑ j, if p ∈ S i ∩ S j then 1 else 0 := by
        intro p
        simp only [hr, sq, Finset.sum_mul_sum, ite_zero_mul_ite_zero, mul_one, Finset.mem_inter]
      simp only [e]
      rw [Finset.sum_comm, Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
      simp only [hc]
      calc _ ≤ ∑ _i : Fin m, (d + (m - 1)) := Finset.sum_le_sum (fun i _ => hrow i)
        _ = m * (d + (m - 1)) := by simp
    have cs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun p : Fin N => (Finset.univ.filter fun i => p ∈ S i).card)
    rw [hsum, Finset.card_univ, Fintype.card_fin] at cs
    have h2 : (m * d) ^ 2 ≤ N * (m * (d + (m - 1))) := cs.trans (Nat.mul_le_mul_left _ hsq)
    have h3 : m * d * d ≤ N * (d + (m - 1)) := by
      apply Nat.le_of_mul_le_mul_left _ hm
      calc m * (m * d * d) = (m * d) ^ 2 := by ring
        _ ≤ N * (m * (d + (m - 1))) := h2
        _ = m * (N * (d + (m - 1))) := by ring
    have h4 : N * (m + d) = N * (d + (m - 1)) + N := by
      rw [show m + d = (d + (m - 1)) + 1 by omega]
      ring
    omega
