import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2407

theorem wit {N M : ℕ} (I : Fin N → Fin M → Prop) (L : Set (Fin M))
    (hno : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (p q z : Fin N) (hpq : p ≠ q) (hq : 3 ≤ {l : Fin M | l ∈ L ∧ I q l}.ncard)
    (hz : L ⊆ {l2 : Fin M | I p l2 ∨ I z l2}) : z = q := by
  by_contra hzq
  have h3 : 2 < {l : Fin M | l ∈ L ∧ I q l}.ncard := hq
  rw [Set.two_lt_ncard (Set.toFinite _)] at h3
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := h3
  have key : ∀ l l' : Fin M, l ≠ l' → I q l → I q l' →
      ¬ (I p l ∧ I p l') ∧ ¬ (I z l ∧ I z l') := by
    intro l l' hl h1 h2
    exact ⟨fun h => hno p q l l' hpq hl ⟨h.1, h1, h.2, h2⟩,
      fun h => hno z q l l' hzq hl ⟨h.1, h1, h.2, h2⟩⟩
  have kab := key a b hab ha.2 hb.2
  have kac := key a c hac ha.2 hc.2
  have kbc := key b c hbc hb.2 hc.2
  have za := hz ha.1
  have zb := hz hb.1
  have zc := hz hc.1
  simp only [Set.mem_setOf_eq] at za zb zc
  tauto

end PEqualNP.Outside.L_meta_2407

theorem PEqualNP.Outside.L_meta_2407 : ∀ (N M : ℕ) (I : Fin N → Fin M → Prop) (L : Set (Fin M)), (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → {p : Fin N | 3 ≤ {l : Fin M | l ∈ L ∧ I p l}.ncard ∧ ∃ z : Fin N, L ⊆ {l2 : Fin M | I p l2 ∨ I z l2}}.ncard ≤ 2 := by
  intro N M I L hno
  by_contra hcon
  have h3 : 2 < {p : Fin N | 3 ≤ {l : Fin M | l ∈ L ∧ I p l}.ncard ∧ ∃ z : Fin N, L ⊆ {l2 : Fin M | I p l2 ∨ I z l2}}.ncard := by
    omega
  rw [Set.two_lt_ncard (Set.toFinite _)] at h3
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := h3
  obtain ⟨z, hz⟩ := ha.2
  have h1 := PEqualNP.Outside.L_meta_2407.wit I L hno a b z hab hb.1 hz
  have h2 := PEqualNP.Outside.L_meta_2407.wit I L hno a c z hac hc.1 hz
  exact hbc (h1.symm.trans h2)
