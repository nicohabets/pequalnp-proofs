import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1473

/-- Doubling is injective modulo an odd number. -/
theorem dbl_inj (k : ℕ) (hodd : (k + 1) % 2 = 1) (a b : Fin (k + 1)) (h : a + a = b + b) :
    a = b := by
  have h' := congrArg Fin.val h
  rw [Fin.val_add, Fin.val_add] at h'
  have h2 : 2 * a.val ≡ 2 * b.val [MOD (k + 1)] := by
    unfold Nat.ModEq; rw [two_mul, two_mul]; exact h'
  have hc : Nat.Coprime 2 (k + 1) := by
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
  have h3 : a.val ≡ b.val [MOD (k + 1)] := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc) h2
  unfold Nat.ModEq at h3
  rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at h3
  exact Fin.ext h3

theorem main (k s : ℕ) (hodd : (k + 1) % 2 = 1) (D : Finset (Fin (k + 1)))
    (hD : D.card = s) (hs : (s + 1).choose 2 < k + 1) :
    ∃ c : Fin (k + 1), c ∉ D ∧ ∀ t u : Fin (k + 1), ¬ (t + c - u ∈ D ∧ u + c - t ∈ D) := by
  classical
  let sums : Finset (Fin (k + 1)) :=
    D.sym2.image (Sym2.lift ⟨fun a b => a + b, fun a b => add_comm a b⟩)
  have hcard : sums.card < (Finset.univ.image fun c : Fin (k + 1) => c + c).card := by
    rw [Finset.card_image_of_injective _ (fun a b h => dbl_inj k hodd a b h)]
    calc sums.card ≤ D.sym2.card := Finset.card_image_le
      _ = (s + 1).choose 2 := by rw [Finset.card_sym2, hD]
      _ < k + 1 := hs
      _ = (Finset.univ : Finset (Fin (k + 1))).card := by simp
  obtain ⟨x, hx, hxn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
  have key : ∀ d1 ∈ D, ∀ d2 ∈ D, d1 + d2 ≠ c + c := by
    intro d1 h1 d2 h2 he
    apply hxn
    rw [← he]
    exact Finset.mem_image.2 ⟨s(d1, d2), Finset.mk_mem_sym2_iff.2 ⟨h1, h2⟩, rfl⟩
  refine ⟨c, fun hc => key c hc c hc rfl, ?_⟩
  rintro t u ⟨h1, h2⟩
  exact key _ h1 _ h2 (by abel)

end PEqualNP.Outside.L_meta_1473

theorem PEqualNP.Outside.L_meta_1473 : ∀ (q : ℕ) (D : Finset (Fin (q ^ 2 + q + 1))),
    2 ≤ q → D.card = q + 1 →
    ∃ c : Fin (q ^ 2 + q + 1), c ∉ D ∧
      ∀ t u : Fin (q ^ 2 + q + 1), ¬ (t + c - u ∈ D ∧ u + c - t ∈ D) := by
  intro q D hq hD
  refine PEqualNP.Outside.L_meta_1473.main (q ^ 2 + q) (q + 1) ?_ D hD ?_
  · have : (q ^ 2 + q) % 2 = 0 := by
      have : q ^ 2 + q = q * (q + 1) := by ring
      rw [this]; exact Nat.even_iff.1 (Nat.even_mul_succ_self q)
    omega
  · rw [Nat.choose_two_right]
    have h1 : (q + 1 + 1) * (q + 1 + 1 - 1) = q ^ 2 + 3 * q + 2 := by
      simp only [Nat.add_sub_cancel]; ring
    rw [h1]
    have : q ^ 2 ≥ 2 * q := by nlinarith
    omega
