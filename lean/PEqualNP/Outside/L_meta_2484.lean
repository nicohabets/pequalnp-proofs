import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2484 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (∀ pl ∈ A, (∃ j_1 a_1 b_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [a_1, b_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [b_1, a_1])) ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_1 : Fin n => decide (k_1.val = pw a_2)) = true} = {pl.1} ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (b_1) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {pl.2})) → A.card ≤ 2 * {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  classical
  intro n N M pw lw C A _ hA
  let G : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let S : Finset ℕ := (Finset.range C.gates.length).filter
    (fun ja => (G ja).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  have hS : {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and} = (S : Set ℕ) := by
    ext ja
    simp [S, G]
  rw [hS, Set.ncard_coe_finset]
  let g : ℕ × Bool → ℕ × ℕ := fun p =>
    if p.2 = true then ((G p.1).inputs.getD 0 0, (G p.1).inputs.getD 1 0)
    else ((G p.1).inputs.getD 1 0, (G p.1).inputs.getD 0 0)
  have key : ∀ e ∈ A, ∃ p : ℕ × Bool, p ∈ S ×ˢ (Finset.univ : Finset Bool) ∧
      {a_2 | PEqualNP.CleanedNonEdge.wireVal n C ((g p).1) (fun k_1 : Fin n => decide (k_1.val = pw a_2)) = true} = {e.1} ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C ((g p).2) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {e.2} := by
    intro e he
    obtain ⟨j, a, b, ⟨hj, hop, hab⟩, h1, h2⟩ := hA e he
    have hjS : j ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj, hop⟩
    rcases hab with hab | hab
    · have ha : (G j).inputs.getD 0 0 = a := by
        show (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0 = a
        rw [hab]; rfl
      have hb : (G j).inputs.getD 1 0 = b := by
        show (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0 = b
        rw [hab]; rfl
      refine ⟨(j, true), by simp [hjS], ?_, ?_⟩
      · have : (g (j, true)).1 = a := ha
        rw [this]; exact h1
      · have : (g (j, true)).2 = b := hb
        rw [this]; exact h2
    · have ha : (G j).inputs.getD 1 0 = a := by
        show (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0 = a
        rw [hab]; rfl
      have hb : (G j).inputs.getD 0 0 = b := by
        show (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0 = b
        rw [hab]; rfl
      refine ⟨(j, false), by simp [hjS], ?_, ?_⟩
      · have : (g (j, false)).1 = a := ha
        rw [this]; exact h1
      · have : (g (j, false)).2 = b := hb
        rw [this]; exact h2
  choose f hf using key
  have hle : A.attach.card ≤ (S ×ˢ (Finset.univ : Finset Bool)).card := by
    refine Finset.card_le_card_of_injOn (fun e => f e.1 e.2) ?_ ?_
    · intro e _
      exact (hf e.1 e.2).1
    · intro e1 _ e2 _ heq
      have h1 := (hf e1.1 e1.2).2
      have h2 := (hf e2.1 e2.2).2
      have heq' : f e1.1 e1.2 = f e2.1 e2.2 := heq
      rw [heq'] at h1
      have a1 : ({(e1.1).1} : Set (Fin N)) = {(e2.1).1} := h1.1.symm.trans h2.1
      have a2 : ({(e1.1).2} : Set (Fin M)) = {(e2.1).2} := h1.2.symm.trans h2.2
      rw [Set.singleton_eq_singleton_iff] at a1 a2
      exact Subtype.ext (Prod.ext a1 a2)
  rw [Finset.card_attach, Finset.card_product, Finset.card_univ, Fintype.card_bool] at hle
  omega
