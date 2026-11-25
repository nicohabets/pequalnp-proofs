import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_209

/-! The Karchmer-Wigderson walk. For a formula `φ`, a set `p` of inputs where `φ` is true and a
set `q` of inputs where `φ` is false, induction on `φ` builds a typing of the pairs in `p x q`
whose literal matrices (restricted to `p x q`) have rank sum at most the leaf count. At a leaf
`(j, c)` the typing is constantly `j`; only the literal `(j, c)` has a nonzero matrix, an outer
product of indicators, of rank at most one. At an AND node the false side is split by the value
of the left child, at an OR node the true side is; each literal matrix is then the sum of the
two matrices from the children, and rank is subadditive. -/

open PEqualNP.MetaComplexity

/-- Literal matrix restricted to the pairs in `p x q`. -/
def M (n : ℕ) (p q : (Fin n → Bool) → Bool) (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ)
    (i : Fin n) (b : Bool) : Matrix (Fin n → Bool) (Fin n → Bool) ℚ :=
  fun x y => if p x = true ∧ q y = true ∧ τ x y = (i : ℕ) ∧ x i = b then 1 else 0

theorem rank_add_le' {m k : Type} [Fintype m] [Fintype k] (A B : Matrix m k ℚ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem lit_eval {n : ℕ} (j : Fin n) (c : Bool) (x : Fin n → Bool) :
    (DMFormula.lit j c).eval x = true ↔ x j = c := by
  cases c <;> simp [DMFormula.eval]

theorem key (n : ℕ) (φ : DMFormula n) : ∀ p q : (Fin n → Bool) → Bool,
    (∀ x, p x = true → φ.eval x = true) → (∀ y, q y = true → φ.eval y = false) →
    ∃ τ : (Fin n → Bool) → (Fin n → Bool) → ℕ,
      (∀ x y, p x = true → q y = true → ∃ i : Fin n, τ x y = (i : ℕ) ∧ x i ≠ y i) ∧
      (∑ i : Fin n, ∑ b : Bool, (M n p q τ i b).rank) ≤ φ.leaves := by
  induction φ with
  | lit j c =>
    intro p q hp hq
    have hpx : ∀ x, p x = true → x j = c := fun x hx => (lit_eval j c x).1 (hp x hx)
    have hqy : ∀ y, q y = true → y j ≠ c := fun y hy h => by
      have := hq y hy
      rw [← Bool.not_eq_true, lit_eval] at this
      exact this h
    refine ⟨fun _ _ => j, fun x y hx hy => ⟨j, rfl, by rw [hpx x hx]; exact (hqy y hy).symm⟩, ?_⟩
    have hz : ∀ (i : Fin n) (b : Bool), ¬ (i = j ∧ b = c) → M n p q (fun _ _ => j) i b = 0 := by
      intro i b hib
      ext x y
      simp only [M, Matrix.zero_apply]
      split_ifs with h
      · exfalso
        obtain ⟨h1, _, h3, h4⟩ := h
        have hi : i = j := Fin.ext h3.symm
        subst hi
        exact hib ⟨rfl, by rw [← h4, hpx x h1]⟩
      · rfl
    have h1 : M n p q (fun _ _ => j) j c =
        Matrix.vecMulVec (fun x : Fin n → Bool => if p x = true then (1 : ℚ) else 0)
          (fun y : Fin n → Bool => if q y = true then (1 : ℚ) else 0) := by
      ext x y
      simp only [M, Matrix.vecMulVec_apply]
      by_cases hx : p x = true <;> by_cases hy : q y = true <;> simp [hx, hy, hpx]
    rw [Finset.sum_eq_single j, Finset.sum_eq_single c, h1]
    · exact Matrix.rank_vecMulVec_le _ _
    · intro b _ hb
      rw [hz j b (fun h => hb h.2), Matrix.rank_zero]
    · simp
    · intro i _ hi
      exact Finset.sum_eq_zero (fun b _ => by rw [hz i b (fun h => hi h.1), Matrix.rank_zero])
    · simp
  | and φ ψ ihφ ihψ =>
    intro p q hp hq
    obtain ⟨τ1, ht1, hs1⟩ := ihφ p (fun y => q y && !φ.eval y)
      (fun x hx => by have := hp x hx; simp [DMFormula.eval] at this; exact this.1)
      (fun y hy => by simp at hy; exact hy.2)
    obtain ⟨τ2, ht2, hs2⟩ := ihψ p (fun y => q y && φ.eval y)
      (fun x hx => by have := hp x hx; simp [DMFormula.eval] at this; exact this.2)
      (fun y hy => by
        simp at hy
        have := hq y hy.1
        simp [DMFormula.eval, hy.2] at this
        exact this)
    refine ⟨fun x y => if φ.eval y = true then τ2 x y else τ1 x y, ?_, ?_⟩
    · intro x y hx hy
      by_cases hφ : φ.eval y = true
      · simp only [hφ, if_true]; exact ht2 x y hx (by simp [hy, hφ])
      · simp only [hφ]; exact ht1 x y hx (by simp [hy, hφ])
    · have hsplit : ∀ i b, M n p q (fun x y => if φ.eval y = true then τ2 x y else τ1 x y) i b =
          M n p (fun y => q y && !φ.eval y) τ1 i b + M n p (fun y => q y && φ.eval y) τ2 i b := by
        intro i b
        ext x y
        by_cases hφ : φ.eval y = true <;> simp [M, hφ]
      calc _ ≤ ∑ i : Fin n, ∑ b : Bool, ((M n p (fun y => q y && !φ.eval y) τ1 i b).rank +
              (M n p (fun y => q y && φ.eval y) τ2 i b).rank) := by
            gcongr with i _ b _
            rw [hsplit i b]
            exact rank_add_le' _ _
        _ = (∑ i : Fin n, ∑ b : Bool, (M n p (fun y => q y && !φ.eval y) τ1 i b).rank) +
              ∑ i : Fin n, ∑ b : Bool, (M n p (fun y => q y && φ.eval y) τ2 i b).rank := by
            simp only [Finset.sum_add_distrib]
        _ ≤ (DMFormula.and φ ψ).leaves := by
            simp only [DMFormula.leaves]; omega
  | or φ ψ ihφ ihψ =>
    intro p q hp hq
    obtain ⟨τ1, ht1, hs1⟩ := ihφ (fun x => p x && φ.eval x) q
      (fun x hx => by simp at hx; exact hx.2)
      (fun y hy => by have := hq y hy; simp [DMFormula.eval] at this; exact this.1)
    obtain ⟨τ2, ht2, hs2⟩ := ihψ (fun x => p x && !φ.eval x) q
      (fun x hx => by
        simp at hx
        have := hp x hx.1
        simp [DMFormula.eval, hx.2] at this
        exact this)
      (fun y hy => by have := hq y hy; simp [DMFormula.eval] at this; exact this.2)
    refine ⟨fun x y => if φ.eval x = true then τ1 x y else τ2 x y, ?_, ?_⟩
    · intro x y hx hy
      by_cases hφ : φ.eval x = true
      · simp only [hφ, if_true]; exact ht1 x y (by simp [hx, hφ]) hy
      · simp only [hφ]; exact ht2 x y (by simp [hx, hφ]) hy
    · have hsplit : ∀ i b, M n p q (fun x y => if φ.eval x = true then τ1 x y else τ2 x y) i b =
          M n (fun x => p x && φ.eval x) q τ1 i b + M n (fun x => p x && !φ.eval x) q τ2 i b := by
        intro i b
        ext x y
        by_cases hφ : φ.eval x = true <;> simp [M, hφ]
      calc _ ≤ ∑ i : Fin n, ∑ b : Bool, ((M n (fun x => p x && φ.eval x) q τ1 i b).rank +
              (M n (fun x => p x && !φ.eval x) q τ2 i b).rank) := by
            gcongr with i _ b _
            rw [hsplit i b]
            exact rank_add_le' _ _
        _ = (∑ i : Fin n, ∑ b : Bool, (M n (fun x => p x && φ.eval x) q τ1 i b).rank) +
              ∑ i : Fin n, ∑ b : Bool, (M n (fun x => p x && !φ.eval x) q τ2 i b).rank := by
            simp only [Finset.sum_add_distrib]
        _ ≤ (DMFormula.or φ ψ).leaves := by
            simp only [DMFormula.leaves]; omega

end PEqualNP.Outside.L_meta_209

theorem PEqualNP.Outside.L_meta_209 :
∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ),
    PEqualNP.MetaComplexity.HasLeafSize n f s → PEqualNP.MetaComplexity.HasTypedRank n f s
 := by
  open PEqualNP.Outside.L_meta_209 PEqualNP.MetaComplexity in
  intro n f s ⟨φ, hl, hφ⟩
  obtain ⟨τ, h1, h2⟩ := key n φ f (fun y => !f y) (fun x hx => by rw [hφ]; exact hx)
    (fun y hy => by rw [hφ]; simpa using hy)
  refine ⟨τ, fun x y hx hy => h1 x y hx (by simp [hy]), ?_⟩
  have hM : ∀ i b, typedMatrix n f τ i b = M n f (fun y => !f y) τ i b := by
    intro i b
    ext x y
    simp [typedMatrix, M]
  simp only [hM]
  omega
