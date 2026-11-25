import Mathlib
import PEqualNP.Defs

/-
Monotone wire-comparison lemmas (step, R, fold_R, R_append, R_ofFn) adapted from the merged
proof of L-meta-8841 by BastianMIllan.
Idea: with at most one NOT gate, write the circuit as G(z, NOT H(z)) with G and H monotone.
The values at the all-false and all-true inputs force G(z, true) = true and G(z, false) = false
for every z, so the circuit computes NOT H and the gates before the NOT gate compute H.
-/

namespace PEqualNP.Outside.L_meta_6318

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem and_mono (a a' b b' : Bool) (h1 : a ≤ a') (h2 : b ≤ b') : (a && b) ≤ (a' && b') := by
  revert h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem or_mono (a a' b b' : Bool) (h1 : a ≤ a') (h2 : b ≤ b') : (a || b) ≤ (a' || b') := by
  revert h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem all_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) :
    (l.map f).all id ≤ (l.map f').all id := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id]
    exact and_mono _ _ _ _ (h a) ih

theorem any_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) :
    (l.map f).any id ≤ (l.map f').any id := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id]
    exact or_mono _ _ _ _ (h a) ih

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp
  · rw [List.getD_eq_default]
    simp
    omega

def R (W W' : List Bool) : Prop :=
  W.length = W'.length ∧ ∀ i, W.getD i false ≤ W'.getD i false

theorem step_R (W W' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : R W W') : R (step W g) (step W' g) := by
  obtain ⟨hl, hle⟩ := h
  have hv : g.op.eval (g.inputs.map fun i => W.getD i false) ≤
      g.op.eval (g.inputs.map fun i => W'.getD i false) := by
    rcases hg with hg | hg <;> rw [hg] <;> simp only [GateOp.eval]
    · exact all_mono _ _ _ hle
    · exact any_mono _ _ _ hle
  refine ⟨by simp [step, hl], fun i => ?_⟩
  simp only [step, getD_snoc, hl]
  split_ifs
  · exact hle i
  · exact hv
  · exact le_refl _

theorem fold_R (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ W W' : List Bool, R W W' → R (gs.foldl step W) (gs.foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (step_R W W' g (hgs g List.mem_cons_self) h)

theorem R_append {l1 l1' l2 l2' : List Bool} (h1 : R l1 l1') (h2 : R l2 l2') :
    R (l1 ++ l2) (l1' ++ l2') := by
  obtain ⟨hl1, h1⟩ := h1
  obtain ⟨hl2, h2⟩ := h2
  refine ⟨by simp [hl1, hl2], fun i => ?_⟩
  by_cases hi : i < l1.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl1 ▸ hi)]
    exact h1 i
  · have hi' : l1.length ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ hi', List.getD_append_right _ _ _ _ (hl1 ▸ hi'), hl1]
    exact h2 _

theorem R_ofFn {n : ℕ} (f g : Fin n → Bool) (h : ∀ i, f i ≤ g i) :
    R (List.ofFn f) (List.ofFn g) := by
  refine ⟨by simp, fun i => ?_⟩
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn]
    exact h ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem R_single (b c : Bool) (h : b ≤ c) : R [b] [c] := by
  refine ⟨rfl, fun i => ?_⟩
  rcases i with _ | i
  · simpa using h
  · simp

theorem fold_length (gs : List Gate) (z : List Bool) :
    (gs.foldl step z).length = z.length + gs.length := by
  induction gs generalizing z with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem true_of_le {a b : Bool} (h : a ≤ b) (ha : a = true) : b = true := by
  revert h ha; cases a <;> cases b <;> decide

theorem false_of_le {a b : Bool} (h : a ≤ b) (hb : b = false) : a = false := by
  revert h hb; cases a <;> cases b <;> decide

theorem not_headD (g : Gate) (W : List Bool) (N : ℕ) (hN : W.length ≤ N) (hg : g.op = GateOp.not) :
    g.op.eval (g.inputs.map fun j => W.getD j false) = !(W.getD (g.inputs.headD N) false) := by
  rw [hg]
  simp only [GateOp.eval]
  cases h : g.inputs with
  | nil =>
    simp only [List.map_nil, List.headD_nil]
    rw [List.getD_eq_default _ _ hN]
  | cons a l => simp

def inp {n : ℕ} (a b : Fin n) (x : Fin n → Bool) : List Bool := List.ofFn x ++ [x a || x b]

theorem inp_length {n : ℕ} (a b : Fin n) (x : Fin n → Bool) : (inp a b x).length = n + 1 := by
  simp [inp]

theorem R_inp {n : ℕ} (a b : Fin n) (x y : Fin n → Bool) (h : ∀ i, x i ≤ y i) :
    R (inp a b x) (inp a b y) :=
  R_append (R_ofFn x y h) (R_single _ _ (or_mono _ _ _ _ (h a) (h b)))

theorem main (n : ℕ) (a b : Fin n) (C : Circuit) (f : (Fin n → Bool) → Bool)
    (hF : PEqualNP.MetaComplexity.FanInTwo C) (hN : PEqualNP.NotBracket.notCount C ≤ 1)
    (h0 : f (fun _ => false) = false) (h1 : f (fun _ => true) = true)
    (hC : ∀ x : Fin n → Bool, (!C.eval (inp a b x)) = f x) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, D.eval (inp a b x) = f x := by
  obtain ⟨gs, o⟩ := C
  have hops : ∀ g ∈ gs, g.op ≠ GateOp.not → g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg hne
    have := (hF g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hne
  have hR0 : ∀ x : Fin n → Bool, R (inp a b (fun _ => false)) (inp a b x) :=
    fun x => R_inp a b _ _ (fun i => by cases x i <;> decide)
  have hR1 : ∀ x : Fin n → Bool, R (inp a b x) (inp a b (fun _ => true)) :=
    fun x => R_inp a b _ _ (fun i => by cases x i <;> decide)
  have e0 := hC (fun _ => false)
  have e1 := hC (fun _ => true)
  rw [h0] at e0
  rw [h1] at e1
  by_cases hex : ∃ g ∈ gs, g.op = GateOp.not
  · obtain ⟨g, hg, hgn⟩ := hex
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
    let _ : DecidableEq GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
    have hc := hN
    simp only [PEqualNP.NotBracket.notCount, List.filter_append, List.filter_cons, hgn,
      decide_true, ite_true, List.length_append, List.length_cons] at hc
    have hp : (List.filter (fun g => decide (g.op = GateOp.not)) pre).length = 0 := by omega
    have hq : (List.filter (fun g => decide (g.op = GateOp.not)) post).length = 0 := by omega
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at hp hq
    have hpreM : ∀ g' ∈ pre, g'.op = GateOp.and ∨ g'.op = GateOp.or := by
      intro g' hg'
      exact hops g' (by simp [hg']) (by simpa using hp g' hg')
    have hpostM : ∀ g' ∈ post, g'.op = GateOp.and ∨ g'.op = GateOp.or := by
      intro g' hg'
      exact hops g' (by simp [hg']) (by simpa using hq g' hg')
    let N := n + 1 + (pre ++ g :: post).length
    let i := g.inputs.headD N
    let P : List Bool → List Bool := fun z => pre.foldl step z
    let H : List Bool → Bool := fun z => (P z).getD i false
    let G : Bool → List Bool → Bool := fun y z => (post.foldl step (P z ++ [y])).getD o false
    have hmono : ∀ y y' z z', y ≤ y' → R z z' → G y z ≤ G y' z' := by
      intro y y' z z' hy hz
      exact (fold_R post hpostM _ _ (R_append (fold_R pre hpreM _ _ hz) (R_single _ _ hy))).2 o
    have hevalC : ∀ x : Fin n → Bool,
        Circuit.eval ⟨pre ++ g :: post, o⟩ (inp a b x) = G (!H (inp a b x)) (inp a b x) := by
      intro x
      show (List.foldl step (inp a b x) (pre ++ g :: post)).getD o false = _
      rw [List.foldl_append, List.foldl_cons]
      have hl : (P (inp a b x)).length ≤ N := by
        simp only [P, fold_length, inp_length, N, List.length_append, List.length_cons]
        omega
      simp only [G, H, step]
      rw [not_headD g (pre.foldl step (inp a b x)) N hl hgn]
    rw [hevalC] at e0 e1
    have hH0 : H (inp a b (fun _ => false)) = false := by
      by_contra hc
      have hc' : H (inp a b (fun _ => false)) = true := by simpa using hc
      rw [hc'] at e0
      have hG : G false (inp a b (fun _ => false)) = true := by simpa using e0
      have := true_of_le (hmono false (!H (inp a b (fun _ => true))) _ _ (by simp)
        (hR0 (fun _ => true))) hG
      simp at e1
      rw [this] at e1
      simp at e1
    have hGt : G true (inp a b (fun _ => false)) = true := by
      rw [hH0] at e0; simpa using e0
    have hH1 : H (inp a b (fun _ => true)) = true := by
      by_contra hc
      have hc' : H (inp a b (fun _ => true)) = false := by simpa using hc
      rw [hc'] at e1
      have := true_of_le (hmono true true _ _ (le_refl _) (hR0 (fun _ => true))) hGt
      simp at e1
      rw [this] at e1
      simp at e1
    have hGf : G false (inp a b (fun _ => true)) = false := by
      rw [hH1] at e1; simpa using e1
    refine ⟨⟨pre, i⟩, ?_, ?_, ?_⟩
    · intro g' hg'
      refine ⟨?_, (hF g' (by simp [hg'])).2⟩
      rcases hpreM g' hg' with h | h <;> simp [h]
    · simp [Circuit.size]
    · intro x
      have hD : Circuit.eval ⟨pre, i⟩ (inp a b x) = H (inp a b x) := rfl
      rw [hD, ← hC x, hevalC]
      cases hx : H (inp a b x)
      · have := true_of_le (hmono true true _ _ (le_refl _) (hR0 x)) hGt
        simp [this]
      · have := false_of_le (hmono false false _ _ (le_refl _) (hR1 x)) hGf
        simp [this]
  · push Not at hex
    have hM : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => hops g hg (hex g hg)
    have hle := (fold_R gs hM _ _ (hR0 (fun _ => true))).2 o
    have ha : Circuit.eval ⟨gs, o⟩ (inp a b (fun _ => false)) = true := by simpa using e0
    have hb : Circuit.eval ⟨gs, o⟩ (inp a b (fun _ => true)) = false := by simpa using e1
    have := true_of_le hle ha
    exact absurd (this.symm.trans hb) (by decide)

end PEqualNP.Outside.L_meta_6318

theorem PEqualNP.Outside.L_meta_6318 : ∀ (x1 : ℕ) (x2 x3 : Fin x1) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : (Fin x1 → Bool) → Bool), PEqualNP.MetaComplexity.FanInTwo x4 → PEqualNP.NotBracket.notCount x4 ≤ (1 : ℕ) → (x5 fun (x8 : Fin x1) => Bool.false) = Bool.false → (x5 fun (x9 : Fin x1) => Bool.true) = Bool.true → (∀ (x10 : Fin x1 → Bool), (!x4.eval (List.ofFn x10 ++ [x10 x2 || x10 x3])) = x5 x10) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x11 ∧ x11.size < x4.size ∧ ∀ (x12 : Fin x1 → Bool), x11.eval (List.ofFn x12 ++ [x12 x2 || x12 x3]) = x5 x12 := by
  intro n a b C f hF hN h0 h1 hC
  exact PEqualNP.Outside.L_meta_6318.main n a b C f hF hN h0 h1 hC
