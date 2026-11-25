import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8561 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)), x3.Nonempty → ∃ (x5 : Finset ℕ) (x6 : ℕ → Finset (Fin x1 × Fin x2)), x5 ⊆ Finset.range ((2 : ℕ) * x3.card - (1 : ℕ)) ∧ x6 ((2 : ℕ) * x3.card - (2 : ℕ)) = x3 ∧ x5.card + (1 : ℕ) = x3.card ∧ (∀ x7 ∉ x5, (x6 x7).card ≤ (1 : ℕ)) ∧ ∀ x7 ∈ x5, (2 : ℕ) ≤ x7 ∧ x6 x7 = x6 (x7 - (2 : ℕ)) ∪ x6 (x7 - (1 : ℕ)) := by
  intro n1 n2 E hE
  classical
  obtain ⟨e0, _⟩ := hE
  have hk : 0 < E.card := Finset.card_pos.2 ⟨e0, by assumption⟩
  have hl : E.toList.length = E.card := Finset.length_toList E
  refine ⟨(Finset.range (2 * E.card - 1)).filter (fun j => 2 ≤ j ∧ j % 2 = 0),
    fun j => if 2 * E.card - 2 < j then ∅ else if j % 2 = 1 then {E.toList.getD ((j + 1) / 2) e0}
      else (E.toList.take (j / 2 + 1)).toFinset, Finset.filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · have h1 : ¬ (2 * E.card - 2 < 2 * E.card - 2) := lt_irrefl _
    have h2 : ¬ ((2 * E.card - 2) % 2 = 1) := by omega
    have h3 : (2 * E.card - 2) / 2 + 1 = E.card := by omega
    simp only [h1, h2, if_false, h3]
    rw [← hl, List.take_length, Finset.toList_toFinset]
  · have hJ : (Finset.range (2 * E.card - 1)).filter (fun j => 2 ≤ j ∧ j % 2 = 0)
        = (Finset.range (E.card - 1)).image (fun i => 2 * i + 2) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨j / 2 - 1, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨by omega, by omega, by omega⟩
    rw [hJ, Finset.card_image_of_injective _ (fun a b h => by
      have h' : 2 * a + 2 = 2 * b + 2 := h
      omega),
      Finset.card_range]
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hj
    by_cases h1 : 2 * E.card - 2 < j
    · simp [h1]
    · by_cases h2 : j % 2 = 1
      · simp [h1, h2]
      · have hj0 : j = 0 := by
          by_contra hne
          exact hj (by omega) (by omega) (by omega)
        subst hj0
        have h4 : ¬ (2 * E.card - 2 < 0) := by omega
        show (if 2 * E.card - 2 < 0 then (∅ : Finset (Fin n1 × Fin n2)) else if 0 % 2 = 1 then {E.toList.getD ((0 + 1) / 2) e0}
          else (E.toList.take (0 / 2 + 1)).toFinset).card ≤ 1
        rw [if_neg h4, if_neg (by decide)]
        exact le_trans (List.toFinset_card_le _) (by simp)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨h1, h2, h3⟩ := hj
    refine ⟨h2, ?_⟩
    have a1 : ¬ (2 * E.card - 2 < j) := by omega
    have a2 : ¬ (j % 2 = 1) := by omega
    have b1 : ¬ (2 * E.card - 2 < j - 2) := by omega
    have b2 : ¬ ((j - 2) % 2 = 1) := by omega
    have c1 : ¬ (2 * E.card - 2 < j - 1) := by omega
    have c2 : (j - 1) % 2 = 1 := by omega
    have d1 : (j - 2) / 2 + 1 = j / 2 := by omega
    have d2 : (j - 1 + 1) / 2 = j / 2 := by omega
    have hlt : j / 2 < E.toList.length := by rw [hl]; omega
    simp only [a1, a2, b1, b2, c1, c2, if_false, if_true, d1, d2]
    rw [List.take_succ_eq_append_getElem hlt, List.toFinset_append, List.getD_eq_getElem _ _ hlt]
    simp
