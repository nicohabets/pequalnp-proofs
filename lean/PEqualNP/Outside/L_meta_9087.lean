import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9087

-- A circuit with at most one gate (no gate at index 1) cannot compute the Fano incidence
-- function: its output is an input wire, one AND/OR of two inputs, or a missing wire.

open PEqualNP.CircuitLowerBounds

def Fano (x : Fin 14 → Bool) : Prop :=
  ∃ (p l : Fin 7), (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true

theorem getD_ofFn (x : Fin 14 → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < 14 then x ⟨i, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i < 14 <;> simp [h]

def ind (i : Fin 14) : Fin 14 → Bool := fun j => decide (j = i)

theorem not_fano_ind (i : Fin 14) : ¬ Fano (ind i) := by
  rintro ⟨p, l, -, h1, h2⟩
  simp only [ind, decide_eq_true_eq] at h1 h2
  rw [← h2] at h1
  have := congrArg Fin.val h1
  simp at this
  omega

def pair (p l : Fin 7) : Fin 14 → Bool :=
  fun j => decide (j = Fin.castAdd 7 p ∨ j = Fin.natAdd 7 l)

theorem fano_pair (p l : Fin 7) (h : p = l ∨ p = l + 1 ∨ p = l + 3) : Fano (pair p l) :=
  ⟨p, l, h, by simp [pair], by simp [pair]⟩

theorem avoid : ∀ a b : Fin 14, ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
    Fin.castAdd 7 p ≠ a ∧ Fin.castAdd 7 p ≠ b ∧ Fin.natAdd 7 l ≠ a ∧ Fin.natAdd 7 l ≠ b := by
  decide

def allOn : Fin 14 → Bool := fun _ => true

theorem fano_all : Fano allOn := ⟨0, 0, Or.inl rfl, rfl, rfl⟩

theorem core (C : Circuit) (hao : PEqualNP.TopForm.IsAO2 14 C)
    (hspec : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ Fano x)
    (h1 : ¬ ∃ g : Gate, C.gates[1]? = some g) : False := by
  obtain ⟨hop, hrb, hlen⟩ := hao
  have hle : C.gates.length ≤ 1 := by
    by_contra hc
    exact h1 ⟨C.gates[1]'(by omega), List.getElem?_eq_getElem _⟩
  -- the case where the output is an input wire
  have inputCase : C.output < 14 → (∀ x : Fin 14 → Bool,
      C.eval (List.ofFn x) = (List.ofFn x).getD C.output false) → False := by
    intro ho hev
    have := (hspec (ind ⟨C.output, ho⟩)).mp (by rw [hev, getD_ofFn, dif_pos ho]; simp [ind])
    exact not_fano_ind _ this
  rcases hgs : C.gates with _ | ⟨g, _ | ⟨g', gs⟩⟩
  · -- no gate
    have hev : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = (List.ofFn x).getD C.output false := by
      intro x; simp [Circuit.eval, Circuit.wires, hgs]
    by_cases ho : C.output < 14
    · exact inputCase ho hev
    · have := (hspec allOn).mpr fano_all
      rw [hev, getD_ofFn, dif_neg ho] at this
      exact Bool.false_ne_true this
  · -- one gate
    have hg : g ∈ C.gates := by rw [hgs]; exact List.mem_singleton_self g
    have hgl := hlen g hg
    have hrd : ∀ i ∈ g.inputs, i < 14 := by
      have := hrb 0 (by rw [hgs]; simp)
      simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, hgs] using this
    obtain ⟨a, b, hab⟩ : ∃ a b, g.inputs = [a, b] := by
      match hh : g.inputs, hgl with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    have ha : a < 14 := hrd a (by rw [hab]; simp)
    have hb : b < 14 := hrd b (by rw [hab]; simp)
    have hev : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
        (List.ofFn x ++ [g.op.eval [(List.ofFn x).getD a false, (List.ofFn x).getD b false]]).getD
          C.output false := by
      intro x; simp [Circuit.eval, Circuit.wires, hgs, hab]
    by_cases ho : C.output < 14
    · apply inputCase ho
      intro x
      rw [hev x, List.getD_append _ _ _ _ (by simpa using ho)]
    · by_cases ho14 : C.output = 14
      · have hev' : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
            g.op.eval [(List.ofFn x).getD a false, (List.ofFn x).getD b false] := by
          intro x
          rw [hev x, ho14]
          simp [List.getD_eq_getElem?_getD]
        rcases hop g hg with hand | hor
        · obtain ⟨p, l, hpl, hpa, hpb, hla, hlb⟩ := avoid ⟨a, ha⟩ ⟨b, hb⟩
          have := (hspec (pair p l)).mpr (fano_pair p l hpl)
          rw [hev', hand, getD_ofFn, dif_pos ha, getD_ofFn, dif_pos hb] at this
          simp only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq,
            Bool.and_eq_true, pair, decide_eq_true_eq] at this
          rcases this.1 with h | h
          · exact hpa (h.symm)
          · exact hla (h.symm)
        · have := (hspec (ind ⟨a, ha⟩)).mp (by
            rw [hev', hor, getD_ofFn, dif_pos ha]
            simp [GateOp.eval, ind])
          exact not_fano_ind _ this
      · have := (hspec allOn).mpr fano_all
        rw [hev, List.getD_eq_default _ _ (by simp; omega)] at this
        exact Bool.false_ne_true this
  · have : C.gates.length = gs.length + 2 := by rw [hgs]; simp
    omega

end PEqualNP.Outside.L_meta_9087

theorem PEqualNP.Outside.L_meta_9087 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (26 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) → ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ) (fun (x6 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x6)) [((0 : ℕ), (7 : ℕ))] → (¬∃ (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x7) → False :=
  fun C _ hao _ hspec _ h1 => PEqualNP.Outside.L_meta_9087.core C hao hspec h1
