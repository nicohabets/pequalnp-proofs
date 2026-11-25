import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_gct_154 : ∀ (R : Type) [CommRing R] (g e f : R), (g + e) ^ 3 + (g - e) ^ 3 + 2 * (e ^ 2 * f - g) ^ 3 = 6 * e ^ 2 * g * (1 + f * g) - 6 * e ^ 4 * g * f ^ 2 + 2 * e ^ 6 * f ^ 3 := by
  intro R _ g e f
  ring
