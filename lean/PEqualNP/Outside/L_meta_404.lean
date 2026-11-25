import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_404

/-! The only edge at the leaf l is lw. An edge whose ends are both on after the update either is lw (then its value is b AND x_w, or x_w when x_l is set to 1) or avoids l and reads x unchanged; with x_l = 1, an edge at w is absorbed by x_w; with x_w = 0, no edge at w is on. -/

end PEqualNP.Outside.L_meta_404

theorem PEqualNP.Outside.L_meta_404 :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (l w : Fin n), G.Adj l w → (∀ v : Fin n, G.Adj l v → v = w) → ∀ x : Fin n → Bool, (∀ b : Bool, (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) (Function.update x l b) = ((b && x w) || decide (∃ u v : Fin n, G.Adj u v ∧ u ≠ l ∧ v ≠ l ∧ x u = true ∧ x v = true))) ∧ (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) (Function.update x l true) = (x w || decide (∃ u v : Fin n, G.Adj u v ∧ u ≠ l ∧ u ≠ w ∧ v ≠ l ∧ v ≠ w ∧ x u = true ∧ x v = true)) ∧ (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) (Function.update x w false) = decide (∃ u v : Fin n, G.Adj u v ∧ u ≠ w ∧ v ≠ w ∧ x u = true ∧ x v = true) := by
  intro n G _ l w hlw hleaf x
  have hwl : w ≠ l := hlw.ne.symm
  have nbr : ∀ v, G.Adj v l → v = w := fun v h => hleaf v h.symm
  refine ⟨fun b => ?_, ?_, ?_⟩
  · apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Function.update_apply]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      by_cases hul : u = l
      · subst hul
        have := hleaf v huv
        subst this
        rw [if_pos rfl] at hu
        rw [if_neg hwl] at hv
        exact Or.inl ⟨hu, hv⟩
      · by_cases hvl : v = l
        · subst hvl
          have := nbr u huv
          subst this
          rw [if_pos rfl] at hv
          rw [if_neg hul] at hu
          exact Or.inl ⟨hv, hu⟩
        · rw [if_neg hul] at hu
          rw [if_neg hvl] at hv
          exact Or.inr ⟨u, v, huv, hul, hvl, hu, hv⟩
    · rintro (⟨hb, hw⟩ | ⟨u, v, huv, hul, hvl, hu, hv⟩)
      · exact ⟨l, w, hlw, by rw [if_pos rfl]; exact hb, by rw [if_neg hwl]; exact hw⟩
      · exact ⟨u, v, huv, by rw [if_neg hul]; exact hu, by rw [if_neg hvl]; exact hv⟩
  · apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, decide_eq_true_eq, Function.update_apply]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      by_cases hul : u = l
      · subst hul
        have := hleaf v huv
        subst this
        rw [if_neg hwl] at hv
        exact Or.inl hv
      · by_cases hvl : v = l
        · subst hvl
          have := nbr u huv
          subst this
          rw [if_neg hul] at hu
          exact Or.inl hu
        · rw [if_neg hul] at hu
          rw [if_neg hvl] at hv
          by_cases huw : u = w
          · subst huw; exact Or.inl hu
          · by_cases hvw : v = w
            · subst hvw; exact Or.inl hv
            · exact Or.inr ⟨u, v, huv, hul, huw, hvl, hvw, hu, hv⟩
    · rintro (hw | ⟨u, v, huv, hul, _, hvl, _, hu, hv⟩)
      · exact ⟨l, w, hlw, by rw [if_pos rfl], by rw [if_neg hwl]; exact hw⟩
      · exact ⟨u, v, huv, by rw [if_neg hul]; exact hu, by rw [if_neg hvl]; exact hv⟩
  · apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq, Function.update_apply]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      by_cases huw : u = w
      · rw [if_pos huw] at hu; exact absurd hu (by simp)
      · by_cases hvw : v = w
        · rw [if_pos hvw] at hv; exact absurd hv (by simp)
        · rw [if_neg huw] at hu
          rw [if_neg hvw] at hv
          exact ⟨u, v, huv, huw, hvw, hu, hv⟩
    · rintro ⟨u, v, huv, huw, hvw, hu, hv⟩
      exact ⟨u, v, huv, by rw [if_neg huw]; exact hu, by rw [if_neg hvw]; exact hv⟩
