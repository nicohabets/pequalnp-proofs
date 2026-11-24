import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1707

def lines : List (Finset (Fin 21)) := [{1, 5, 9, 13, 17}, {0, 5, 6, 7, 8}, {2, 5, 10, 15, 20}, {4, 5, 12, 14, 19}, {3, 5, 11, 16, 18}, {0, 1, 2, 3, 4}, {1, 6, 10, 14, 18}, {1, 8, 12, 16, 20}, {1, 7, 11, 15, 19}, {0, 9, 10, 11, 12}, {2, 6, 9, 16, 19}, {4, 8, 9, 15, 18}, {3, 7, 9, 14, 20}, {0, 17, 18, 19, 20}, {3, 6, 12, 15, 17}, {2, 8, 11, 14, 17}, {4, 7, 10, 16, 17}, {0, 13, 14, 15, 16}, {4, 6, 11, 13, 20}, {3, 8, 10, 13, 19}, {2, 7, 12, 13, 18}]

theorem bad : ∀ a ∈ ({0, 6, 7, 8} : Finset (Fin 21)), ∀ b ∈ ({2, 10, 15, 20} : Finset (Fin 21)),
    ∃ m ∈ lines, ((3 : Fin 21) ∈ m ∧ (4 : Fin 21) ∈ m ∧ (11 : Fin 21) ∈ m) ∨
      ((3 : Fin 21) ∈ m ∧ (4 : Fin 21) ∈ m ∧ a ∈ m) ∨ ((3 : Fin 21) ∈ m ∧ (4 : Fin 21) ∈ m ∧ b ∈ m) ∨
      ((3 : Fin 21) ∈ m ∧ (11 : Fin 21) ∈ m ∧ a ∈ m) ∨ ((3 : Fin 21) ∈ m ∧ (11 : Fin 21) ∈ m ∧ b ∈ m) ∨
      ((4 : Fin 21) ∈ m ∧ (11 : Fin 21) ∈ m ∧ a ∈ m) ∨ ((4 : Fin 21) ∈ m ∧ (11 : Fin 21) ∈ m ∧ b ∈ m) ∨
      ((3 : Fin 21) ∈ m ∧ a ∈ m ∧ b ∈ m) ∨ ((4 : Fin 21) ∈ m ∧ a ∈ m ∧ b ∈ m) ∨
      ((11 : Fin 21) ∈ m ∧ a ∈ m ∧ b ∈ m) := by
  decide +kernel

theorem dist : ∀ a ∈ ({0, 6, 7, 8} : Finset (Fin 21)), ∀ b ∈ ({2, 10, 15, 20} : Finset (Fin 21)),
    a ≠ 3 ∧ a ≠ 4 ∧ a ≠ 11 ∧ b ≠ 3 ∧ b ≠ 4 ∧ b ≠ 11 ∧ a ≠ b := by
  intro a ha b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;>
    exact absurd (congrArg Fin.val h) (by simp)

theorem three (A m : Finset (Fin 21)) (x y z : Fin 21) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) (hxm : x ∈ m) (hym : y ∈ m) (hzm : z ∈ m) :
    3 ≤ (A ∩ m).card := by
  have hsub : ({x, y, z} : Finset (Fin 21)) ⊆ A ∩ m := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact Finset.mem_inter.2 ⟨hx, hxm⟩
    · exact Finset.mem_inter.2 ⟨hy, hym⟩
    · exact Finset.mem_inter.2 ⟨hz, hzm⟩
  have hc : ({x, y, z} : Finset (Fin 21)).card = 3 :=
    Finset.card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have := Finset.card_le_card hsub
  omega

end PEqualNP.Outside.L_meta_1707

open PEqualNP.Outside.L_meta_1707 in
theorem PEqualNP.Outside.L_meta_1707 : (∀ A : Finset (Fin 21), (∀ m ∈ ([{1, 5, 9, 13, 17}, {0, 5, 6, 7, 8}, {2, 5, 10, 15, 20}, {4, 5, 12, 14, 19}, {3, 5, 11, 16, 18}, {0, 1, 2, 3, 4}, {1, 6, 10, 14, 18}, {1, 8, 12, 16, 20}, {1, 7, 11, 15, 19}, {0, 9, 10, 11, 12}, {2, 6, 9, 16, 19}, {4, 8, 9, 15, 18}, {3, 7, 9, 14, 20}, {0, 17, 18, 19, 20}, {3, 6, 12, 15, 17}, {2, 8, 11, 14, 17}, {4, 7, 10, 16, 17}, {0, 13, 14, 15, 16}, {4, 6, 11, 13, 20}, {3, 8, 10, 13, 19}, {2, 7, 12, 13, 18}] : List (Finset (Fin 21))), (A ∩ m).card ≤ 2) ∧ (∀ p ∈ A, p ∉ ({1, 5, 9, 13, 17} : Finset (Fin 21))) ∧ ({3, 4, 11} : Finset (Fin 21)) ⊆ A → (A ∩ ({0, 6, 7, 8} : Finset (Fin 21)) = ∅ ∨ A ∩ ({2, 10, 15, 20} : Finset (Fin 21)) = ∅)) ∧ ∃ A : Finset (Fin 21), (∀ m ∈ ([{1, 5, 9, 13, 17}, {0, 5, 6, 7, 8}, {2, 5, 10, 15, 20}, {4, 5, 12, 14, 19}, {3, 5, 11, 16, 18}, {0, 1, 2, 3, 4}, {1, 6, 10, 14, 18}, {1, 8, 12, 16, 20}, {1, 7, 11, 15, 19}, {0, 9, 10, 11, 12}, {2, 6, 9, 16, 19}, {4, 8, 9, 15, 18}, {3, 7, 9, 14, 20}, {0, 17, 18, 19, 20}, {3, 6, 12, 15, 17}, {2, 8, 11, 14, 17}, {4, 7, 10, 16, 17}, {0, 13, 14, 15, 16}, {4, 6, 11, 13, 20}, {3, 8, 10, 13, 19}, {2, 7, 12, 13, 18}] : List (Finset (Fin 21))), (A ∩ m).card ≤ 2) ∧ (∀ p ∈ A, p ∉ ({1, 5, 9, 13, 17} : Finset (Fin 21))) ∧ ({3, 4, 11} : Finset (Fin 21)) ⊆ A := by
  have h34 : (3 : Fin 21) ≠ 4 := by decide
  have h311 : (3 : Fin 21) ≠ 11 := by decide
  have h411 : (4 : Fin 21) ≠ 11 := by decide
  constructor
  · rintro A ⟨harc, _, hsub⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hcon
    rw [Finset.mem_inter] at ha hb
    have m3 : (3 : Fin 21) ∈ A := hsub (by simp)
    have m4 : (4 : Fin 21) ∈ A := hsub (by simp)
    have m11 : (11 : Fin 21) ∈ A := hsub (by simp)
    obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := dist a ha.2 b hb.2
    obtain ⟨m, hm, hcase⟩ := bad a ha.2 b hb.2
    have h2 := harc m hm
    have key : 3 ≤ (A ∩ m).card := by
      rcases hcase with ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩ |
        ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩
      · exact three A m 3 4 11 h34 h311 h411 m3 m4 m11 x y z
      · exact three A m 3 4 a h34 (Ne.symm d1) (Ne.symm d2) m3 m4 ha.1 x y z
      · exact three A m 3 4 b h34 (Ne.symm d4) (Ne.symm d5) m3 m4 hb.1 x y z
      · exact three A m 3 11 a h311 (Ne.symm d1) (Ne.symm d3) m3 m11 ha.1 x y z
      · exact three A m 3 11 b h311 (Ne.symm d4) (Ne.symm d6) m3 m11 hb.1 x y z
      · exact three A m 4 11 a h411 (Ne.symm d2) (Ne.symm d3) m4 m11 ha.1 x y z
      · exact three A m 4 11 b h411 (Ne.symm d5) (Ne.symm d6) m4 m11 hb.1 x y z
      · exact three A m 3 a b (Ne.symm d1) (Ne.symm d4) d7 m3 ha.1 hb.1 x y z
      · exact three A m 4 a b (Ne.symm d2) (Ne.symm d5) d7 m4 ha.1 hb.1 x y z
      · exact three A m 11 a b (Ne.symm d3) (Ne.symm d6) d7 m11 ha.1 hb.1 x y z
    omega
  · refine ⟨{3, 4, 11}, ?_, ?_, Finset.Subset.refl _⟩
    · intro m hm
      have hm' : m ∈ PEqualNP.Outside.L_meta_1707.lines := hm
      simp only [PEqualNP.Outside.L_meta_1707.lines, List.mem_cons, List.not_mem_nil, or_false] at hm'
      rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · decide
