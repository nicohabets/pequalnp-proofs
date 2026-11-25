import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6927

/-! A circuit with no gate 1 has at most one gate, so its output is a function of at most two
wires. Of the four incident pairs (i, i) for i < 4, which use disjoint wires, one avoids the
fixed-off wire and both read wires; turning on just that pair must be accepted, while the
all-off input, equal on the two read wires, must be rejected. -/

open PEqualNP.CircuitLowerBounds in
/-- A circuit with at most one gate, of at most two inputs, outputs a function of two wires. -/
theorem small_eval (C : Circuit) (n : ℕ) (hg : C.gates.length ≤ 1)
    (hin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ (F : Bool → Bool → Bool) (a b : ℕ), ∀ L : List Bool, L.length = n →
      C.eval L = F (L.getD a false) (L.getD b false) := by
  rcases hl : C.gates with _ | ⟨g, _ | ⟨g2, t⟩⟩
  · refine ⟨fun p _ => p, C.output, C.output, fun L _ => ?_⟩
    simp only [Circuit.eval, Circuit.wires, hl, List.foldl]
  · have hlen : g.inputs.length ≤ 2 := hin g (by simp [hl])
    have hev : ∀ L : List Bool, C.eval L =
        (L ++ [g.op.eval (g.inputs.map fun i => L.getD i false)]).getD C.output false := by
      intro L
      simp only [Circuit.eval, Circuit.wires, hl, List.foldl]
    by_cases ho : C.output < n
    · refine ⟨fun p _ => p, C.output, C.output, fun L hL => ?_⟩
      rw [hev, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [hL]; exact ho)]
    · by_cases ho' : C.output = n
      · have hv : ∀ L : List Bool, L.length = n → C.eval L =
            g.op.eval (g.inputs.map fun i => L.getD i false) := by
          intro L hL
          rw [hev, ho', List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hL]),
            hL]
          simp
        rcases hi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
        · exact ⟨fun _ _ => g.op.eval [], 0, 0, fun L hL => by rw [hv L hL, hi]; rfl⟩
        · exact ⟨fun p _ => g.op.eval [p], a, a, fun L hL => by rw [hv L hL, hi]; rfl⟩
        · exact ⟨fun p q => g.op.eval [p, q], a, b, fun L hL => by rw [hv L hL, hi]; rfl⟩
        · rw [hi] at hlen; simp at hlen
      · refine ⟨fun _ _ => false, 0, 0, fun L hL => ?_⟩
        rw [hev, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hL]; omega)]
        rfl
  · rw [hl] at hg; simp at hg

end PEqualNP.Outside.L_meta_6927

theorem PEqualNP.Outside.L_meta_6927 :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 x2 = Bool.false → (x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) → (¬∃ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5) → (58 : ℕ) ≤ x1.size := by
  open PEqualNP.Outside.L_meta_6927 PEqualNP.CircuitLowerBounds in
  intro x1 x2 hmono hf hnone
  have hlen : x1.gates.length ≤ 1 := by
    by_contra h
    exact hnone ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨F, a, b, hF⟩ := small_eval x1 26 hlen (fun g hg => (hmono g hg).2)
  have hp : ∃ p : ℕ, p < 4 ∧ p ≠ x2.val ∧ p ≠ a ∧ p ≠ b ∧ 13 + p ≠ x2.val ∧ 13 + p ≠ a ∧
      13 + p ≠ b := by
    by_cases h0 : 0 ≠ x2.val ∧ 0 ≠ a ∧ 0 ≠ b ∧ 13 + 0 ≠ x2.val ∧ 13 + 0 ≠ a ∧ 13 + 0 ≠ b
    · exact ⟨0, by omega, h0⟩
    by_cases h1 : 1 ≠ x2.val ∧ 1 ≠ a ∧ 1 ≠ b ∧ 13 + 1 ≠ x2.val ∧ 13 + 1 ≠ a ∧ 13 + 1 ≠ b
    · exact ⟨1, by omega, h1⟩
    by_cases h2 : 2 ≠ x2.val ∧ 2 ≠ a ∧ 2 ≠ b ∧ 13 + 2 ≠ x2.val ∧ 13 + 2 ≠ a ∧ 13 + 2 ≠ b
    · exact ⟨2, by omega, h2⟩
    by_cases h3 : 3 ≠ x2.val ∧ 3 ≠ a ∧ 3 ≠ b ∧ 13 + 3 ≠ x2.val ∧ 13 + 3 ≠ a ∧ 13 + 3 ≠ b
    · exact ⟨3, by omega, h3⟩
    exfalso; omega
  obtain ⟨p, hp4, hpx, hpa, hpb, hqx, hqa, hqb⟩ := hp
  set x : Fin 26 → Bool := fun k => decide (k.val = p ∨ k.val = 13 + p) with hxdef
  set y : Fin 26 → Bool := fun _ => false with hydef
  have hxc : ∀ c : ℕ, c ≠ p → c ≠ 13 + p → (List.ofFn x).getD c false = false := by
    intro c h1 h2
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    by_cases hc : c < 26
    · simp [hc, hxdef, h1, h2]
    · simp [hc]
  have hyc : ∀ c : ℕ, (List.ofFn y).getD c false = false := by
    intro c
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    by_cases hc : c < 26
    · simp [hc, hydef]
    · simp [hc]
  have hx2 : x x2 = false := by simp [hxdef]; omega
  have hy2 : y x2 = false := rfl
  have ex : x1.eval (List.ofFn x) = true := by
    rw [hf x hx2]
    refine ⟨⟨p, by omega⟩, ⟨p, by omega⟩, Or.inl rfl, ?_, ?_⟩
    · simp [hxdef]
    · simp [hxdef]; omega
  have ey : x1.eval (List.ofFn y) ≠ true := by
    rw [ne_eq, hf y hy2]
    rintro ⟨_, _, _, h, _⟩
    simp [hydef] at h
  have e1 := hF (List.ofFn x) (by simp)
  have e2 := hF (List.ofFn y) (by simp)
  rw [hxc a hpa.symm hqa.symm, hxc b hpb.symm hqb.symm] at e1
  rw [hyc, hyc] at e2
  exact absurd (e2.trans (e1.symm.trans ex)) ey
