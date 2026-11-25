import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1303

/-! All three facts are finite checks over Fin 9, done by kernel evaluation. -/

end PEqualNP.Outside.L_meta_1303

theorem PEqualNP.Outside.L_meta_1303 :
(∀ p p2 l l2 : Fin 9, p ≠ p2 → l ≠ l2 → ¬ ((p.val % 3 = ((l.val / 3) * (p.val / 3) + l.val % 3) % 3) ∧ (p.val % 3 = ((l2.val / 3) * (p.val / 3) + l2.val % 3) % 3) ∧ (p2.val % 3 = ((l.val / 3) * (p2.val / 3) + l.val % 3) % 3) ∧ (p2.val % 3 = ((l2.val / 3) * (p2.val / 3) + l2.val % 3) % 3))) ∧ (∀ l : Fin 9, (Finset.univ.filter (fun p : Fin 9 => (p.val % 3 = ((l.val / 3) * (p.val / 3) + l.val % 3) % 3))).card = 3) ∧ (∀ p : Fin 9, (Finset.univ.filter (fun l : Fin 9 => (p.val % 3 = ((l.val / 3) * (p.val / 3) + l.val % 3) % 3))).card = 3) := by
  set_option synthInstance.maxSize 100000 in
  set_option synthInstance.maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  decide +kernel
