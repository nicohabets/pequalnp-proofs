import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2408

theorem three {N M : ℕ} (I : Fin N → Fin M → Prop) (Wl : Finset (Fin M))
    (mk : Fin M → Finset (Fin N)) (z : Fin N → Fin N)
    (hno : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (hmk : ∀ w ∈ Wl, 3 ≤ (mk w).card ∧ ∀ a ∈ mk w, I a w ∧ ¬ I (z a) w ∧ z a ≠ a)
    (hall : ∀ w ∈ Wl, ∀ a ∈ mk w, ∀ w' ∈ Wl, I a w' ∨ I (z a) w')
    (c : Fin N) (u v w : Fin M) (hu : u ∈ Wl) (hv : v ∈ Wl) (hw : w ∈ Wl)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (cu : I c u) (cv : I c v) (cw : I c w) : False := by
  obtain ⟨hcard, hm⟩ := hmk w hw
  obtain ⟨b, hb, hbc⟩ := Finset.exists_mem_ne (by omega : 1 < (mk w).card) c
  obtain ⟨bw, zbw, -⟩ := hm b hb
  have hzc : z b ≠ c := by
    intro h
    rw [h] at zbw
    exact zbw cw
  have zu : I (z b) u := by
    rcases hall w hw b hb u hu with h | h
    · exact absurd ⟨h, cu, bw, cw⟩ (hno b c u w hbc huw)
    · exact h
  have zv : I (z b) v := by
    rcases hall w hw b hb v hv with h | h
    · exact absurd ⟨h, cv, bw, cw⟩ (hno b c v w hbc hvw)
    · exact h
  exact hno (z b) c u v hzc huv ⟨zu, cu, zv, cv⟩

end PEqualNP.Outside.L_meta_2408

theorem PEqualNP.Outside.L_meta_2408 : ∀ (N M : ℕ) (I : Fin N → Fin M → Prop) (Wl : Finset (Fin M)) (mk : Fin M → Finset (Fin N)) (z : Fin N → Fin N), (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ w ∈ Wl, 3 ≤ (mk w).card ∧ ∀ a ∈ mk w, I a w ∧ ¬ I (z a) w ∧ z a ≠ a) → (∀ w ∈ Wl, ∀ a ∈ mk w, ∀ w' ∈ Wl, I a w' ∨ I (z a) w') → Wl.card ≤ 4 := by
  classical
  intro N M I Wl mk z hno hmk hall
  rcases Finset.eq_empty_or_nonempty Wl with he | ⟨w, hw⟩
  · simp [he]
  obtain ⟨hcard, hm⟩ := hmk w hw
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (mk w).card)
  have two : ∀ c : Fin N, (Wl.filter (fun l => I c l)).card ≤ 2 := by
    intro c
    by_contra hc
    have h3 : 2 < (Wl.filter (fun l => I c l)).card := by omega
    rw [Finset.two_lt_card] at h3
    obtain ⟨u, hu, v, hv, x, hx, huv, hux, hvx⟩ := h3
    rw [Finset.mem_filter] at hu hv hx
    exact PEqualNP.Outside.L_meta_2408.three I Wl mk z hno hmk hall c u v x hu.1 hv.1 hx.1 huv hux hvx hu.2 hv.2 hx.2
  have hsub : Wl ⊆ Wl.filter (fun l => I a l) ∪ Wl.filter (fun l => I (z a) l) := by
    intro l hl
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hall w hw a ha l hl with h | h
    · exact Or.inl ⟨hl, h⟩
    · exact Or.inr ⟨hl, h⟩
  calc Wl.card ≤ (Wl.filter (fun l => I a l) ∪ Wl.filter (fun l => I (z a) l)).card := Finset.card_le_card hsub
    _ ≤ (Wl.filter (fun l => I a l)).card + (Wl.filter (fun l => I (z a) l)).card := Finset.card_union_le _ _
    _ ≤ 4 := by
      have h1 := two a
      have h2 := two (z a)
      omega
