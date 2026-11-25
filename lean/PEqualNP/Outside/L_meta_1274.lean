import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1274

/-! With no gates the wire list is the list of input degrees, and input i (below n) has degree 1 exactly when it is marked. -/

end PEqualNP.Outside.L_meta_1274

theorem PEqualNP.Outside.L_meta_1274 :
∀ (n i : ℕ) (marked : Finset ℕ), i < n → ({ gates := [], output := i } : PEqualNP.CircuitLowerBounds.Circuit).lineDeg n marked = (if i ∈ marked then 1 else 0) := by
  intro n i marked hi
  simp [PEqualNP.CircuitLowerBounds.Circuit.lineDeg, PEqualNP.CircuitLowerBounds.Circuit.lineDegrees,
    List.getD_eq_getElem?_getD, hi]
