import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_799

-- A circuit with fewer than 2 gates is a union of output vertices and one AND of two vertex sets; a finite check
-- over all such circuits shows none is false on every maximal independent set I and true on
-- every I + u.

open PEqualNP.AndCount

def adjB (a b : Fin 5) : Bool :=
  decide ((a.val, b.val) ∈ ([(0, 2), (1, 3), (2, 4), (3, 4)] : List (ℕ × ℕ)) ∨ (b.val, a.val) ∈ ([(0, 2), (1, 3), (2, 4), (3, 4)] : List (ℕ × ℕ)))

def Cond (f : Finset (Fin 5) → Bool) : Bool := decide (
  ∀ I : Finset (Fin 5), (∀ v ∈ I, ∀ w ∈ I, adjB v w = false) → (∀ u, u ∉ I → ∃ v ∈ I, adjB u v = true) →
    f I = false ∧ ∀ u, u ∉ I → f (insert u I) = true)

theorem adj_iff (G : SimpleGraph (Fin 5)) (hG : G.edgeSet = {s(0, 2), s(1, 3), s(2, 4), s(3, 4)}) (a b : Fin 5) :
    G.Adj a b ↔ adjB a b = true := by
  rw [← SimpleGraph.mem_edgeSet, hG]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  revert a b
  decide

theorem no_zero : ∀ (O : Finset (Fin 5)), Cond (fun U => decide (∃ v ∈ O, v ∈ U)) = false := by
  decide +kernel

def maskSet (k : ℕ) : Finset (Fin 5) := Finset.univ.filter (fun i : Fin 5 => k.testBit i.val)

theorem mask_all : ∀ L : Finset (Fin 5), ∃ k < 32, maskSet k = L := by
  decide +kernel

theorem chunk_0 : ∀ k < 4, ∀ (O R : Finset (Fin 5)) (b : Bool),
    Cond (fun U => decide ((∃ v ∈ O, v ∈ U) ∨ (b = true ∧ (∃ v ∈ maskSet (4 * 0 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U)))) = false := by
  decide +kernel

theorem chunk_1 : ∀ k < 4, ∀ (O R : Finset (Fin 5)) (b : Bool),
    Cond (fun U => decide ((∃ v ∈ O, v ∈ U) ∨ (b = true ∧ (∃ v ∈ maskSet (4 * 1 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U)))) = false := by
  decide +kernel

theorem chunk_2 : ∀ k < 4, ∀ (O R : Finset (Fin 5)) (b : Bool),
    Cond (fun U => decide ((∃ v ∈ O, v ∈ U) ∨ (b = true ∧ (∃ v ∈ maskSet (4 * 2 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U)))) = false := by
  decide +kernel

theorem chunk_3 : ∀ k < 4, ∀ (O R : Finset (Fin 5)) (b : Bool),
    Cond (fun U => decide ((∃ v ∈ O, v ∈ U) ∨ (b = true ∧ (∃ v ∈ maskSet (4 * 3 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U)))) = false := by
  decide +kernel

theorem chunk_4 : ∀ k < 4, ∀ (O R : Finset (Fin 5)) (b : Bool),
    Cond (fun U => decide ((∃ v ∈ O, v ∈ U) ∨ (b = true ∧ (∃ v ∈ maskSet (4 * 4 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U)))) = false := by
  decide +kernel

theorem chunk_5 : ∀ k < 4, ∀ (O R : Finset (Fin 5)) (b : Bool),
    Cond (fun U => decide ((∃ v ∈ O, v ∈ U) ∨ (b = true ∧ (∃ v ∈ maskSet (4 * 5 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U)))) = false := by
  decide +kernel

theorem chunk_6 : ∀ k < 4, ∀ (O R : Finset (Fin 5)) (b : Bool),
    Cond (fun U => decide ((∃ v ∈ O, v ∈ U) ∨ (b = true ∧ (∃ v ∈ maskSet (4 * 6 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U)))) = false := by
  decide +kernel

theorem chunk_7 : ∀ k < 4, ∀ (O R : Finset (Fin 5)) (b : Bool),
    Cond (fun U => decide ((∃ v ∈ O, v ∈ U) ∨ (b = true ∧ (∃ v ∈ maskSet (4 * 7 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U)))) = false := by
  decide +kernel

theorem no_one : ∀ (O L R : Finset (Fin 5)) (b : Bool),
    Cond (fun U => decide ((∃ v ∈ O, v ∈ U) ∨ (b = true ∧ (∃ v ∈ L, v ∈ U) ∧ (∃ v ∈ R, v ∈ U)))) = false := by
  intro O L R b
  obtain ⟨k, hk, rfl⟩ := mask_all L
  have h4 : k = 4 * (k / 4) + k % 4 := by omega
  rw [h4]
  have hr : k % 4 < 4 := Nat.mod_lt _ (by omega)
  have hq : k / 4 < 8 := by omega
  interval_cases hkq : k / 4
  · exact chunk_0 _ hr O R b
  · exact chunk_1 _ hr O R b
  · exact chunk_2 _ hr O R b
  · exact chunk_3 _ hr O R b
  · exact chunk_4 _ hr O R b
  · exact chunk_5 _ hr O R b
  · exact chunk_6 _ hr O R b
  · exact chunk_7 _ hr O R b

theorem main (G : SimpleGraph (Fin 5)) (hG : G.edgeSet = {s(0, 2), s(1, 3), s(2, 4), s(3, 4)})
    (C : AndCountCircuit 5)
    (H : ∀ I : Finset (Fin 5), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
      C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) : 2 ≤ C.size := by
  have hc : Cond (fun U => C.eval U) = true := by
    simp only [Cond, decide_eq_true_eq]
    intro I h1 h2
    apply H I
    · intro v hv w hw ha
      rw [adj_iff G hG] at ha
      rw [h1 v hv w hw] at ha
      exact Bool.false_ne_true ha
    · intro u hu
      obtain ⟨v, hv, ha⟩ := h2 u hu
      exact ⟨v, hv, (adj_iff G hG u v).mpr ha⟩
  by_contra hlt
  obtain ⟨sz, lv, lg, rv, rg, ov, og⟩ := C
  simp only at hlt
  rcases sz with _ | _ | sz
  · have he : ∀ U, AndCountCircuit.eval ⟨0, lv, lg, rv, rg, ov, og⟩ U = decide (∃ v ∈ ov, v ∈ U) := by
      intro U
      simp [AndCountCircuit.eval]
    have hc' : Cond (fun U => decide (∃ v ∈ ov, v ∈ U)) = true := by
      have : (fun U => AndCountCircuit.eval ⟨0, lv, lg, rv, rg, ov, og⟩ U) = _ := funext he
      rw [← this]; exact hc
    rw [no_zero ov] at hc'; exact Bool.false_ne_true hc'
  · have he : ∀ U, AndCountCircuit.eval ⟨1, lv, lg, rv, rg, ov, og⟩ U =
        decide ((∃ v ∈ ov, v ∈ U) ∨ (decide ((0 : Fin 1) ∈ og) = true ∧ (∃ v ∈ lv 0, v ∈ U) ∧
          (∃ v ∈ rv 0, v ∈ U))) := by
      intro U
      simp [AndCountCircuit.eval, AndCountCircuit.gateVal, AndCountCircuit.gateValFuel,
        AndCountCircuit.sideTrue, Fin.exists_fin_one]
    have hc' : Cond (fun U => decide ((∃ v ∈ ov, v ∈ U) ∨ (decide ((0 : Fin 1) ∈ og) = true ∧
        (∃ v ∈ lv 0, v ∈ U) ∧ (∃ v ∈ rv 0, v ∈ U)))) = true := by
      have : (fun U => AndCountCircuit.eval ⟨1, lv, lg, rv, rg, ov, og⟩ U) = _ := funext he
      rw [← this]; exact hc
    rw [no_one ov (lv 0) (rv 0) _] at hc'; exact Bool.false_ne_true hc'
  · omega

end PEqualNP.Outside.L_meta_799

theorem PEqualNP.Outside.L_meta_799 : ∀ G : SimpleGraph (Fin 5), G.edgeSet = {s(0, 2), s(1, 3), s(2, 4), s(3, 4)} → ∀ C : PEqualNP.AndCount.AndCountCircuit 5, C.WellFormed → (∀ I : Finset (Fin 5), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) → 2 ≤ C.size :=
  fun G hG C _ H => PEqualNP.Outside.L_meta_799.main G hG C H
