import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_843

-- A circuit with fewer than 2 gates is a union of output vertices and one AND of two vertex sets; a finite check
-- over all such circuits shows none is false on every maximal independent set I and true on
-- every I + u.

open PEqualNP.AndCount

def adjB (a b : Fin 7) : Bool :=
  decide ((a.val, b.val) ∈ ([(0, 5), (1, 5), (2, 6), (3, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∨ (b.val, a.val) ∈ ([(0, 5), (1, 5), (2, 6), (3, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)))

def Cond (f : Finset (Fin 7) → Bool) : Bool := decide (
  ∀ I : Finset (Fin 7), (∀ v ∈ I, ∀ w ∈ I, adjB v w = false) → (∀ u, u ∉ I → ∃ v ∈ I, adjB u v = true) →
    f I = false ∧ ∀ u, u ∉ I → f (insert u I) = true)

theorem adj_iff (G : SimpleGraph (Fin 7)) (hG : G.edgeSet = {s(0, 5), s(1, 5), s(2, 6), s(3, 6), s(4, 6), s(5, 6)}) (a b : Fin 7) :
    G.Adj a b ↔ adjB a b = true := by
  rw [← SimpleGraph.mem_edgeSet, hG]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  revert a b
  decide

theorem no_zero : ∀ (O : Finset (Fin 7)), Cond (fun U => decide (∃ v ∈ O, v ∈ U)) = false := by
  decide +kernel

def maskSet (k : ℕ) : Finset (Fin 7) := Finset.univ.filter (fun i : Fin 7 => k.testBit i.val)

theorem mask_all : ∀ L : Finset (Fin 7), ∃ k < 128, maskSet k = L := by
  decide +kernel

theorem mis_cover : ∀ v : Fin 7, ∃ I : Finset (Fin 7), (∀ a ∈ I, ∀ b ∈ I, adjB a b = false) ∧
    (∀ u, u ∉ I → ∃ w ∈ I, adjB u w = true) ∧ v ∈ I := by
  decide +kernel

theorem chunk_0 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 0 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_1 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 1 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_2 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 2 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_3 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 3 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_4 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 4 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_5 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 5 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_6 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 6 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_7 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 7 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_8 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 8 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_9 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 9 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_10 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 10 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_11 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 11 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_12 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 12 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_13 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 13 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_14 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 14 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem chunk_15 : ∀ k < 8, ∀ (R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ maskSet (8 * 15 + k), v ∈ U) ∧
      (∃ v ∈ R, v ∈ U))) = false := by
  decide +kernel

theorem no_one : ∀ (L R : Finset (Fin 7)) (b : Bool),
    Cond (fun U => decide (b = true ∧ (∃ v ∈ L, v ∈ U) ∧ (∃ v ∈ R, v ∈ U))) = false := by
  intro L R b
  obtain ⟨k, hk, rfl⟩ := mask_all L
  have h4 : k = 8 * (k / 8) + k % 8 := by omega
  rw [h4]
  have hr : k % 8 < 8 := Nat.mod_lt _ (by omega)
  have hq : k / 8 < 16 := by omega
  interval_cases hkq : k / 8
  · exact chunk_0 _ hr R b
  · exact chunk_1 _ hr R b
  · exact chunk_2 _ hr R b
  · exact chunk_3 _ hr R b
  · exact chunk_4 _ hr R b
  · exact chunk_5 _ hr R b
  · exact chunk_6 _ hr R b
  · exact chunk_7 _ hr R b
  · exact chunk_8 _ hr R b
  · exact chunk_9 _ hr R b
  · exact chunk_10 _ hr R b
  · exact chunk_11 _ hr R b
  · exact chunk_12 _ hr R b
  · exact chunk_13 _ hr R b
  · exact chunk_14 _ hr R b
  · exact chunk_15 _ hr R b

theorem main (G : SimpleGraph (Fin 7)) (hG : G.edgeSet = {s(0, 5), s(1, 5), s(2, 6), s(3, 6), s(4, 6), s(5, 6)})
    (C : AndCountCircuit 7)
    (H : ∀ I : Finset (Fin 7), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
      C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) : 2 ≤ C.size := by
  have hc : Cond (fun U => C.eval U) = true := by
    unfold Cond
    apply decide_eq_true
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
    have hov : ov = ∅ := by
      by_contra hne
      obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨I, h1, h2, hvI⟩ := mis_cover v
      have hI := (H I (fun a ha b hb hab => by
          rw [adj_iff G hG, h1 a ha b hb] at hab; exact Bool.false_ne_true hab)
        (fun u hu => by
          obtain ⟨w, hw, hw'⟩ := h2 u hu
          exact ⟨w, hw, (adj_iff G hG u w).mpr hw'⟩)).1
      rw [he I] at hI
      simp only [decide_eq_false_iff_not, not_or] at hI
      exact hI.1 ⟨v, hv, hvI⟩
    have hc' : Cond (fun U => decide (decide ((0 : Fin 1) ∈ og) = true ∧
        (∃ v ∈ lv 0, v ∈ U) ∧ (∃ v ∈ rv 0, v ∈ U))) = true := by
      have : (fun U => AndCountCircuit.eval ⟨1, lv, lg, rv, rg, ov, og⟩ U) =
          (fun U => decide (decide ((0 : Fin 1) ∈ og) = true ∧
            (∃ v ∈ lv 0, v ∈ U) ∧ (∃ v ∈ rv 0, v ∈ U))) := by
        funext U; rw [he U, hov]; simp
      rw [← this]; exact hc
    rw [no_one (lv 0) (rv 0) _] at hc'; exact Bool.false_ne_true hc'
  · omega

end PEqualNP.Outside.L_meta_843

theorem PEqualNP.Outside.L_meta_843 : ∀ G : SimpleGraph (Fin 7), G.edgeSet = {s(0, 5), s(1, 5), s(2, 6), s(3, 6), s(4, 6), s(5, 6)} → ∀ C : PEqualNP.AndCount.AndCountCircuit 7, C.WellFormed → (∀ I : Finset (Fin 7), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) → 2 ≤ C.size :=
  fun G hG C _ H => PEqualNP.Outside.L_meta_843.main G hG C H
