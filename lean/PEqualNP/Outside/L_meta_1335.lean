import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1335

/-! Two lines share exactly one point, so two distinct points lie on at most one common line,
and by the joining axiom on exactly one. Through a point p, the lines minus p partition the
other q^2 + q points into parts of size q, so p lies on exactly q + 1 lines; summing the point
degrees over z gives the first identity. The ordered pairs of distinct points of z are
partitioned by the line through them, and line i holds |L i ∩ z| (|L i ∩ z| - 1) of them,
which gives the second. -/

end PEqualNP.Outside.L_meta_1335

theorem PEqualNP.Outside.L_meta_1335 :
∀ (q : ℕ) (L : Fin (q ^ 2 + q + 1) → Finset (Fin (q ^ 2 + q + 1))), 2 ≤ q →
  (∀ i : Fin (q ^ 2 + q + 1), (L i).card = q + 1) →
  (∀ i j : Fin (q ^ 2 + q + 1), i ≠ j → (L i ∩ L j).card = 1) →
  (∀ p p' : Fin (q ^ 2 + q + 1), p ≠ p' → ∃ i : Fin (q ^ 2 + q + 1), p ∈ L i ∧ p' ∈ L i) →
  ∀ z : Finset (Fin (q ^ 2 + q + 1)),
    ∑ i : Fin (q ^ 2 + q + 1), (L i ∩ z).card = (q + 1) * z.card ∧
    ∑ i : Fin (q ^ 2 + q + 1), (L i ∩ z).card * ((L i ∩ z).card - 1) = z.card * (z.card - 1) := by
  intro q L hq hcard hint hjoin z
  have huniq : ∀ (p p' : Fin (q ^ 2 + q + 1)) (i j : Fin (q ^ 2 + q + 1)), p ≠ p' → p ∈ L i →
      p' ∈ L i → p ∈ L j → p' ∈ L j → i = j := by
    intro p p' i j hne h1 h2 h3 h4
    by_contra hij
    have hsub : ({p, p'} : Finset (Fin (q ^ 2 + q + 1))) ⊆ L i ∩ L j := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.2 ⟨h1, h3⟩
      · exact Finset.mem_inter.2 ⟨h2, h4⟩
    have h5 := Finset.card_le_card hsub
    rw [Finset.card_pair hne, hint i j hij] at h5
    omega
  have hr : ∀ p, (Finset.univ.filter fun i => p ∈ L i).card = q + 1 := by
    intro p
    have hpart : Finset.univ.erase p =
        (Finset.univ.filter fun i => p ∈ L i).biUnion fun i => (L i).erase p := by
      ext p'
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion,
        Finset.mem_filter, true_and]
      constructor
      · intro hne
        obtain ⟨i, h1, h2⟩ := hjoin p p' (Ne.symm hne)
        exact ⟨i, h1, hne, h2⟩
      · rintro ⟨i, _, hne, _⟩
        exact hne
    have hdisj : ((Finset.univ.filter fun i => p ∈ L i : Finset (Fin (q ^ 2 + q + 1))) :
        Set (Fin (q ^ 2 + q + 1))).PairwiseDisjoint fun i => (L i).erase p := by
      intro i hi j hj hij
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
      rw [Function.onFun, Finset.disjoint_left]
      intro p' h1 h2
      rw [Finset.mem_erase] at h1 h2
      exact hij (huniq p p' i j (Ne.symm h1.1) hi h1.2 hj h2.2)
    have hc := congrArg Finset.card hpart
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_biUnion hdisj] at hc
    have hs : ∀ i ∈ (Finset.univ.filter fun i => p ∈ L i), ((L i).erase p).card = q := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.card_erase_of_mem hi, hcard]
      simp
    rw [Finset.sum_congr rfl hs, Finset.sum_const, smul_eq_mul] at hc
    have hc' : (Finset.univ.filter fun i => p ∈ L i).card * q = (q + 1) * q := by
      rw [← hc]
      ring_nf
      omega
    exact Nat.eq_of_mul_eq_mul_right (by omega) hc'
  constructor
  · have e : ∀ i, (L i ∩ z).card = ∑ p ∈ z, if p ∈ L i then 1 else 0 := by
      intro i
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
    simp only [e]
    rw [Finset.sum_comm]
    have e2 : ∀ p, (∑ i : Fin (q ^ 2 + q + 1), if p ∈ L i then 1 else 0) = q + 1 := by
      intro p
      rw [← Finset.card_filter, hr]
    simp only [e2, Finset.sum_const, smul_eq_mul]
    ring
  · have e : ∀ i, (L i ∩ z).card * ((L i ∩ z).card - 1) = ((L i ∩ z).offDiag).card := by
      intro i
      rw [Finset.offDiag_card, Nat.mul_sub_one]
    simp only [e]
    have hpart : (Finset.univ.biUnion fun i => (L i ∩ z).offDiag) = z.offDiag := by
      ext ⟨a, b⟩
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_offDiag,
        Finset.mem_inter]
      constructor
      · rintro ⟨i, ⟨_, ha⟩, ⟨_, hb⟩, hab⟩
        exact ⟨ha, hb, hab⟩
      · rintro ⟨ha, hb, hab⟩
        obtain ⟨i, h1, h2⟩ := hjoin a b hab
        exact ⟨i, ⟨h1, ha⟩, ⟨h2, hb⟩, hab⟩
    have hdisj : ((Finset.univ : Finset (Fin (q ^ 2 + q + 1))) :
        Set (Fin (q ^ 2 + q + 1))).PairwiseDisjoint fun i => (L i ∩ z).offDiag := by
      intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      rintro ⟨a, b⟩ h1 h2
      simp only [Finset.mem_offDiag, Finset.mem_inter] at h1 h2
      exact hij (huniq a b i j h1.2.2 h1.1.1 h1.2.1.1 h2.1.1 h2.2.1.1)
    rw [← Finset.card_biUnion hdisj, hpart, Finset.offDiag_card, Nat.mul_sub_one]
