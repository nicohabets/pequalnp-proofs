import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_gct_155 : ∀ i : Fin 9, Polynomial.eval ((![1/4, 2/5, 1/2, 3/4, 9/10, 11/10, 3/2, 2, 5/2, 3] : Fin 10 → ℚ) i.castSucc) ((40 * Polynomial.X ^ 7 - 13 * Polynomial.X ^ 9) ^ 3 + (Polynomial.X ^ 11 - Polynomial.X) ^ 3 + (13 * Polynomial.X ^ 3 - 40 * Polynomial.X ^ 5) ^ 3 : Polynomial ℚ) * Polynomial.eval ((![1/4, 2/5, 1/2, 3/4, 9/10, 11/10, 3/2, 2, 5/2, 3] : Fin 10 → ℚ) i.succ) ((40 * Polynomial.X ^ 7 - 13 * Polynomial.X ^ 9) ^ 3 + (Polynomial.X ^ 11 - Polynomial.X) ^ 3 + (13 * Polynomial.X ^ 3 - 40 * Polynomial.X ^ 5) ^ 3 : Polynomial ℚ) < 0 := by
  intro i
  fin_cases i <;> simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow] <;> norm_num
