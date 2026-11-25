import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_206

/-! The constant typing `0` types every pair. Only the literal `(0, true)` has a nonzero
matrix, the outer product of the indicators of `x 0 = true` and `y 0 = false`, so the rank sum
is at most one. Conversely, any typing gives the pair (all true, all false) some literal
`(i, true)`, whose matrix then has an entry `1`, hence rank at least one (a `1 x 1` submatrix
equal to the identity). -/

open PEqualNP.MetaComplexity

theorem one_le_rank {m k : Type} [Fintype k] (A : Matrix m k ℚ) (x : m) (y : k)
    (h : A x y = 1) : 1 ≤ A.rank := by
  have h1 := Matrix.rank_submatrix_le A (fun _ : Fin 1 => x) (fun _ : Fin 1 => y)
  have h2 : A.submatrix (fun _ : Fin 1 => x) (fun _ : Fin 1 => y) = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [h]
  rw [h2, Matrix.rank_one, Fintype.card_fin] at h1
  exact h1

theorem part1 (n : ℕ) : HasTypedRank (n + 1) (fun x => x 0) 1 := by
  refine ⟨fun _ _ => 0, ?_, ?_⟩
  · intro x y hx hy
    exact ⟨0, rfl, by simp_all⟩
  · have hz : ∀ (i : Fin (n + 1)) (b : Bool), ¬ (i = 0 ∧ b = true) →
        typedMatrix (n + 1) (fun x => x 0) (fun _ _ => 0) i b = 0 := by
      intro i b hib
      ext x y
      simp only [typedMatrix, Matrix.zero_apply]
      split_ifs with h
      · exfalso
        obtain ⟨h1, _, h3, h4⟩ := h
        have hi : i = 0 := Fin.ext h3.symm
        subst hi
        exact hib ⟨rfl, by rw [← h4]; exact h1⟩
      · rfl
    have h1 : typedMatrix (n + 1) (fun x => x 0) (fun _ _ => 0) 0 true =
        Matrix.vecMulVec (fun x : Fin (n + 1) → Bool => if x 0 = true then (1 : ℚ) else 0)
          (fun y : Fin (n + 1) → Bool => if y 0 = false then (1 : ℚ) else 0) := by
      ext x y
      simp only [typedMatrix, Matrix.vecMulVec_apply]
      by_cases hx : x 0 = true <;> by_cases hy : y 0 = false <;> simp [hx, hy]
    have h0 : ∀ i : Fin n, ∑ b : Bool,
        (typedMatrix (n + 1) (fun x => x 0) (fun _ _ => 0) i.succ b).rank = 0 := by
      intro i
      rw [Fintype.sum_bool, hz _ _ (by simp [Fin.succ_ne_zero]),
        hz _ _ (by simp [Fin.succ_ne_zero]), Matrix.rank_zero]
    rw [Fin.sum_univ_succ, Fintype.sum_bool, h1, hz 0 false (by simp), Matrix.rank_zero,
      Finset.sum_congr rfl (fun i _ => h0 i), Finset.sum_const_zero]
    have := Matrix.rank_vecMulVec_le
      (fun x : Fin (n + 1) → Bool => if x 0 = true then (1 : ℚ) else 0)
      (fun y : Fin (n + 1) → Bool => if y 0 = false then (1 : ℚ) else 0)
    omega

theorem part2 (n : ℕ) : ¬ HasTypedRank (n + 1) (fun x => x 0) 0 := by
  rintro ⟨τ, hτ, hs⟩
  obtain ⟨i, hi, _⟩ := hτ (fun _ => true) (fun _ => false) rfl rfl
  have h1 : 1 ≤ (typedMatrix (n + 1) (fun x => x 0) τ i true).rank :=
    one_le_rank _ (fun _ => true) (fun _ => false) (by simp [typedMatrix, hi])
  have h2 : (typedMatrix (n + 1) (fun x => x 0) τ i true).rank ≤
      ∑ b : Bool, (typedMatrix (n + 1) (fun x => x 0) τ i b).rank :=
    Finset.single_le_sum (f := fun b => (typedMatrix (n + 1) (fun x => x 0) τ i b).rank)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have h3 : ∑ b : Bool, (typedMatrix (n + 1) (fun x => x 0) τ i b).rank ≤
      ∑ j : Fin (n + 1), ∑ b : Bool, (typedMatrix (n + 1) (fun x => x 0) τ j b).rank :=
    Finset.single_le_sum
      (f := fun j => ∑ b : Bool, (typedMatrix (n + 1) (fun x => x 0) τ j b).rank)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

end PEqualNP.Outside.L_meta_206

theorem PEqualNP.Outside.L_meta_206 :
∀ n : ℕ, PEqualNP.MetaComplexity.HasTypedRank (n + 1) (fun x => x 0) 1 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank (n + 1) (fun x => x 0) 0
 := by
  intro n
  exact ⟨PEqualNP.Outside.L_meta_206.part1 n, PEqualNP.Outside.L_meta_206.part2 n⟩
