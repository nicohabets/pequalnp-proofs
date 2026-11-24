import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2726 : (∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D → (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = true ↔ ∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true) → (∀ w ∈ P, w < N ∨ ∃ i < D.gates.length, w = N + N + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) → (∀ w ∈ L, (N ≤ w ∧ w < N + N) ∨ ∃ i < D.gates.length, w = N + N + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) → (∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) → (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ D.size + 1) → ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → (∀ C0 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) C0 → (∀ z0 : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C0 z0 = decide (∃ p : Fin N, ∃ l : Fin N, I p l ∧ z0 (Fin.castAdd N p) = true ∧ z0 (Fin.natAdd N l) = true)) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p : Fin N, ∃ l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C0.size ∧ (∀ w ∈ P, w < N ∨ ∃ i < D.gates.length, w = N + N + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (N ≤ w ∧ w < N + N) ∨ ∃ i < D.gates.length, w = N + N + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → N * (q + 1) ≤ C.size + 1 := by
  intro H1 q N I _ C hq hN hline huniq H2 hC hCf
  obtain ⟨D, P, L, hD, hDf, hDs, hP, hL, hA⟩ := H2 C hC hCf
  -- distinct points lie on at most one common line, so the incidence graph has no 4-cycle
  have h4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by
    rintro p p' l l' hp hl ⟨h1, h2, h3, h4⟩
    obtain ⟨m, _, hm⟩ := huniq p p' hp
    exact hl ((hm l ⟨h1, h3⟩).trans (hm l' ⟨h2, h4⟩).symm)
  have hmono : PEqualNP.MetaComplexity.Monotone2 D := by
    intro g hg
    refine ⟨?_, (hD.2.2 g hg).le⟩
    rcases hD.1 g hg with h | h <;> simp [h]
  have hiff : ∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = true ↔
      ∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true := by
    intro y
    simp only [hDf y, decide_eq_true_eq]
  have hE := H1 N I D P L h4 hmono hD.2.1 hiff hP hL hA
  -- the number of incident pairs is N (q + 1)
  have hcard : (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card = N * (q + 1) := by
    have hl : ∀ l : Fin N, (∑ p : Fin N, if I p l then 1 else 0) = q + 1 :=
      fun l => (Finset.card_filter _ _).symm.trans (hline l)
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    calc (∑ l : Fin N, ∑ p : Fin N, if I p l then 1 else 0) = ∑ _l : Fin N, (q + 1) :=
          Finset.sum_congr rfl fun l _ => hl l
      _ = N * (q + 1) := by simp
  rw [hcard] at hE
  linarith
