import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_802

-- A circuit with fewer than 1 gates is a union of output vertices; a finite check
-- over all such circuits shows none is false on every maximal independent set I and true on
-- every I + u.

open PEqualNP.AndCount

def adjB (a b : Fin 5) : Bool :=
  decide ((a.val, b.val) ∈ ([(0, 4), (1, 4), (2, 4), (3, 4)] : List (ℕ × ℕ)) ∨ (b.val, a.val) ∈ ([(0, 4), (1, 4), (2, 4), (3, 4)] : List (ℕ × ℕ)))

def Cond (f : Finset (Fin 5) → Bool) : Bool := decide (
  ∀ I : Finset (Fin 5), (∀ v ∈ I, ∀ w ∈ I, adjB v w = false) → (∀ u, u ∉ I → ∃ v ∈ I, adjB u v = true) →
    f I = false ∧ ∀ u, u ∉ I → f (insert u I) = true)

theorem adj_iff (G : SimpleGraph (Fin 5)) (hG : G.edgeSet = {s(0, 4), s(1, 4), s(2, 4), s(3, 4)}) (a b : Fin 5) :
    G.Adj a b ↔ adjB a b = true := by
  rw [← SimpleGraph.mem_edgeSet, hG]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  revert a b
  decide

theorem no_zero : ∀ (O : Finset (Fin 5)), Cond (fun U => decide (∃ v ∈ O, v ∈ U)) = false := by
  decide +kernel

theorem main (G : SimpleGraph (Fin 5)) (hG : G.edgeSet = {s(0, 4), s(1, 4), s(2, 4), s(3, 4)})
    (C : AndCountCircuit 5)
    (H : ∀ I : Finset (Fin 5), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
      C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) : 1 ≤ C.size := by
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
  · omega
  · omega

end PEqualNP.Outside.L_meta_802

theorem PEqualNP.Outside.L_meta_802 : ∀ G : SimpleGraph (Fin 5), G.edgeSet = {s(0, 4), s(1, 4), s(2, 4), s(3, 4)} → ∀ C : PEqualNP.AndCount.AndCountCircuit 5, C.WellFormed → (∀ I : Finset (Fin 5), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) → 1 ≤ C.size :=
  fun G hG C _ H => PEqualNP.Outside.L_meta_802.main G hG C H
