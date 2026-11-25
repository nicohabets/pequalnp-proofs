import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_403

/-! Take a longest path, starting at l with second vertex w. In a forest a path between two adjacent vertices is the edge itself, so a neighbour of a path vertex x that lies further along the path than the next vertex is impossible. Hence l is a leaf (else the path extends at l), and a neighbour v of w other than l and the third path vertex p is off the path; a neighbour u of v other than w would also be off the path, and u, v, w and the rest of the path would be a longer path. -/

open SimpleGraph

theorem lenA {V : Type} {G : SimpleGraph V} (hG : G.IsAcyclic) {x y : V} (h : G.Adj x y)
    (q : G.Walk x y) (hq : q.IsPath) : q.length = 1 := by
  have e := hG.path_unique ⟨q, hq⟩ (SimpleGraph.Path.singleton h)
  have := congrArg (fun r : G.Path x y => r.val.length) e
  simpa using this

theorem lenB {V : Type} [DecidableEq V] {G : SimpleGraph V} (hG : G.IsAcyclic) {x z b y : V}
    (hxz : G.Adj x z) (R : G.Walk z b) (hP : (Walk.cons hxz R).IsPath) (hxy : G.Adj x y)
    (hy : y ∈ R.support) : y = z := by
  rw [Walk.cons_isPath_iff] at hP
  have h1 : (Walk.cons hxz (R.takeUntil y hy)).IsPath := by
    rw [Walk.cons_isPath_iff]
    exact ⟨hP.1.takeUntil hy, fun hx => hP.2 (R.support_takeUntil_subset hy hx)⟩
  have h2 := lenA hG hxy _ h1
  simp only [Walk.length_cons, add_eq_right] at h2
  exact (Walk.eq_of_length_eq_zero h2).symm

theorem core {V : Type} [DecidableEq V] {G : SimpleGraph V} (hG : G.IsAcyclic) {l w b : V}
    (hlw : G.Adj l w) (Q : G.Walk w b) (hP : (Walk.cons hlw Q).IsPath)
    (hmax : ∀ (a c : V) (W : G.Walk a c), W.IsPath → W.length ≤ Q.length + 1) :
    ∃ l w p : V, G.Adj l w ∧ (∀ v : V, G.Adj l v → v = w) ∧
      ∀ v : V, G.Adj w v → v ≠ p → ∀ u : V, G.Adj v u → u = w := by
  have hP' := (Walk.cons_isPath_iff _ _).1 hP
  have leaf : ∀ v, G.Adj l v → v = w := by
    intro v hv
    by_cases hvs : v ∈ (Walk.cons hlw Q).support
    · rw [Walk.support_cons, List.mem_cons] at hvs
      rcases hvs with hvl | hvs
      · exact absurd hvl.symm hv.ne
      · exact lenB hG hlw Q hP hv hvs
    · exfalso
      have := hmax _ _ (Walk.cons hv.symm (Walk.cons hlw Q))
        (by rw [Walk.cons_isPath_iff]; exact ⟨hP, hvs⟩)
      simp at this
  have key : ∀ p : V, (∀ v, G.Adj w v → v ≠ p → v ≠ l → v ∉ Q.support) →
      ∃ l w p : V, G.Adj l w ∧ (∀ v : V, G.Adj l v → v = w) ∧
        ∀ v : V, G.Adj w v → v ≠ p → ∀ u : V, G.Adj v u → u = w := by
    intro p hp
    refine ⟨l, w, p, hlw, leaf, ?_⟩
    intro v hwv hvp u hvu
    by_cases hvl : v = l
    · subst hvl; exact leaf u hvu
    · have hvQ := hp v hwv hvp hvl
      by_contra huw
      have hpath : (Walk.cons hwv.symm Q).IsPath := by
        rw [Walk.cons_isPath_iff]; exact ⟨hP'.1, hvQ⟩
      have huQ : u ∉ Q.support := fun huQ => huw (lenB hG hwv.symm Q hpath hvu huQ)
      have hpath2 : (Walk.cons hvu.symm (Walk.cons hwv.symm Q)).IsPath := by
        rw [Walk.cons_isPath_iff]
        refine ⟨hpath, ?_⟩
        rw [Walk.support_cons, List.mem_cons, not_or]
        exact ⟨hvu.ne.symm, huQ⟩
      have := hmax _ _ _ hpath2
      simp at this
  cases Q with
  | nil =>
    apply key w
    intro v _ hvp _ hvQ
    simp at hvQ
    exact hvp hvQ
  | cons hwp R =>
    apply key _
    intro v hwv hvp _ hvQ
    rw [Walk.support_cons, List.mem_cons] at hvQ
    rcases hvQ with hvw | hvR
    · exact hwv.ne hvw.symm
    · exact hvp (lenB hG hwp R hP'.1 hwv hvR)

end PEqualNP.Outside.L_meta_403

theorem PEqualNP.Outside.L_meta_403 :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.IsAcyclic → (∃ u v : Fin n, G.Adj u v) → ∃ l w p : Fin n, G.Adj l w ∧ (∀ v : Fin n, G.Adj l v → v = w) ∧ ∀ v : Fin n, G.Adj w v → v ≠ p → ∀ u : Fin n, G.Adj v u → u = w := by
  open PEqualNP.Outside.L_meta_403 SimpleGraph in
  intro n G _ hG hex
  obtain ⟨a0, b0, hab⟩ := hex
  classical
  have hbound : ∀ (a b : Fin n) (W : G.Walk a b), W.IsPath → W.length ≤ n := by
    intro a b W hW
    have := hW.length_lt
    simp only [Fintype.card_fin] at this
    omega
  have h1 : ∃ a b : Fin n, ∃ W : G.Walk a b, W.IsPath ∧ W.length = 1 :=
    ⟨a0, b0, Walk.cons hab Walk.nil, by simp [hab.ne], by simp⟩
  have hn : 1 ≤ n := by
    obtain ⟨a, b, W, hW, hl⟩ := h1
    have := hbound a b W hW
    omega
  have hge := Nat.le_findGreatest
    (P := fun k => ∃ a b : Fin n, ∃ W : G.Walk a b, W.IsPath ∧ W.length = k) hn h1
  obtain ⟨l, b, P, hP, hlen⟩ := Nat.findGreatest_spec
    (P := fun k => ∃ a b : Fin n, ∃ W : G.Walk a b, W.IsPath ∧ W.length = k) hn h1
  have hmax : ∀ (a c : Fin n) (W : G.Walk a c), W.IsPath → W.length ≤ P.length := by
    intro a c W hW
    rw [hlen]
    exact Nat.le_findGreatest (hbound a c W hW) ⟨a, c, W, hW, rfl⟩
  cases P with
  | nil => simp at hlen; omega
  | cons hlw Q =>
    exact core hG hlw Q hP (by simpa using hmax)
