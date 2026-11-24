import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3424
open PEqualNP.CircuitLowerBounds

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem app_mono (A A' B B' : List Bool) (hA : A.length = A'.length)
    (ha : ∀ i, A.getD i false = true → A'.getD i false = true)
    (hb : ∀ i, B.getD i false = true → B'.getD i false = true) :
    ∀ i, (A ++ B).getD i false = true → (A' ++ B').getD i false = true := by
  intro i
  by_cases hi : i < A.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hA ▸ hi)]; exact ha i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hA]
    exact hb _

def fl (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [F w g]) w

theorem fl_append (F : List Bool → Gate → Bool) (a b : List Gate) (w : List Bool) :
    fl F (a ++ b) w = fl F b (fl F a w) := by
  simp [fl, List.foldl_append]

theorem fl_cons (F : List Bool → Gate → Bool) (g : Gate) (gs : List Gate) (w : List Bool) :
    fl F (g :: gs) w = fl F gs (w ++ [F w g]) := rfl

def EV (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem pre_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ (U V : List Bool), U.length = V.length →
    (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (fl EV gs U).getD i false = true → (fl EV gs V).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro _ U V _ h i; exact h i
  | cons g gs ih =>
    intro hgs U V hlen h
    rw [fl_cons, fl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · rw [List.length_append, List.length_append, hlen]; rfl
    · apply app_mono U V _ _ hlen h
      intro i
      cases i with
      | zero => exact eval_mono g.op (hgs g List.mem_cons_self) g.inputs U V h
      | succ j => intro h1; simp at h1

theorem not_anti (g : Gate) (hg : g.op = GateOp.not) (A B : List Bool)
    (h : ∀ i, A.getD i false = true → B.getD i false = true) :
    EV A g = false → EV B g = false := by
  unfold EV
  rw [hg]
  cases hin : g.inputs with
  | nil =>
    show (!false) = false → _
    intro h1; cases h1
  | cons a t =>
    show (!(A.getD a false)) = false → (!(B.getD a false)) = false
    intro h1
    have h2 : A.getD a false = true := by
      cases hA : A.getD a false with
      | true => rfl
      | false => rw [hA] at h1; cases h1
    rw [h a h2]; rfl

theorem ev_const (A : List Bool) (c : Bool) : EV A (PEqualNP.NotPremium.constGate c) = c := by
  cases c <;> simp [PEqualNP.NotPremium.constGate, EV, GateOp.eval]

theorem set_same (G : List Gate) (q : ℕ) (hq : q < G.length) (c : Bool) (X : List Bool)
    (h : EV (fl EV (G.take q) X) G[q] = c) :
    fl EV (PEqualNP.NotPremium.replaceByConst G q c) X = fl EV G X := by
  unfold PEqualNP.NotPremium.replaceByConst
  rw [List.set_eq_take_append_cons_drop, if_pos hq]
  conv_rhs => rw [← List.take_append_drop q G, List.drop_eq_getElem_cons hq]
  rw [fl_append, fl_append, fl_cons, fl_cons, h, ev_const]

end PEqualNP.Outside.L_meta_3424

open PEqualNP.Outside.L_meta_3424 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3424 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.NotPremium.AtMostOneNot x2.gates →       ∀ (x5 : Fin x2.gates.length),         (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not →           ∀ (x7 x8 : Fin x1 → Bool),             (∀ (x9 : Fin x1), x7 x9 = Bool.true → x8 x9 = Bool.true) →               have x10 : Bool → (Fin x1 → Bool) → Bool := fun (x10 : Bool) => PEqualNP.MetaComplexity.circuitFun x1 { gates := PEqualNP.NotPremium.replaceByConst x2.gates (↑x5) x10, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit };               (x10 Bool.true x7 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x7 → x10 Bool.false x8 = PEqualNP.MetaComplexity.circuitFun x1 x2 x8) ∧ (x10 Bool.false x8 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x8 → x10 Bool.true x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 x7) := by
  intro n C hF hone q hq x y hxy
  have hq' : q.1 < C.gates.length := q.2
  have hq2 : (C.gates[q.1]).op = GateOp.not := hq
  have hpre : ∀ g ∈ C.gates.take q.1, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hg
    rw [List.getElem_take] at hgi
    have hi2 : i < q.1 := by rw [List.length_take] at hi; omega
    have hi3 : i < C.gates.length := by omega
    have hmem : C.gates[i] ∈ C.gates := List.getElem_mem hi3
    have hop := (hF _ hmem).1
    rw [← hgi]
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      obtain ⟨ι, hι⟩ := hone
      obtain ⟨j, hj⟩ := hι ⟨i, hi3⟩ h
      obtain ⟨j', hj'⟩ := hι q hq
      have hjj : j = j' := Subsingleton.elim _ _
      have he : (⟨i, hi3⟩ : Fin C.gates.length) = q := by rw [← hj, ← hj', hjj]
      have := congrArg Fin.val he
      simp at this
      omega
  have hAB : ∀ i, (fl EV (C.gates.take q.1) (List.ofFn x)).getD i false = true →
      (fl EV (C.gates.take q.1) (List.ofFn y)).getD i false = true :=
    pre_mono _ hpre _ _ (by simp) (ofFn_mono n x y hxy)
  have hv := not_anti C.gates[q.1] hq2 _ _ hAB
  show (_ ≠ _ → _ = _) ∧ (_ ≠ _ → _ = _)
  constructor
  · intro hne
    have hvA : EV (fl EV (C.gates.take q.1) (List.ofFn x)) C.gates[q.1] = false := by
      cases hc : EV (fl EV (C.gates.take q.1) (List.ofFn x)) C.gates[q.1] with
      | false => rfl
      | true =>
        exfalso
        apply hne
        show (fl EV (PEqualNP.NotPremium.replaceByConst C.gates q.1 true) (List.ofFn x)).getD C.output false
          = (fl EV C.gates (List.ofFn x)).getD C.output false
        rw [set_same _ _ hq' true _ hc]
    show (fl EV (PEqualNP.NotPremium.replaceByConst C.gates q.1 false) (List.ofFn y)).getD C.output false
      = (fl EV C.gates (List.ofFn y)).getD C.output false
    rw [set_same _ _ hq' false _ (hv hvA)]
  · intro hne
    have hvA : EV (fl EV (C.gates.take q.1) (List.ofFn x)) C.gates[q.1] = true := by
      cases hc : EV (fl EV (C.gates.take q.1) (List.ofFn x)) C.gates[q.1] with
      | true => rfl
      | false =>
        exfalso
        apply hne
        show (fl EV (PEqualNP.NotPremium.replaceByConst C.gates q.1 false) (List.ofFn y)).getD C.output false
          = (fl EV C.gates (List.ofFn y)).getD C.output false
        rw [set_same _ _ hq' false _ (hv hc)]
    show (fl EV (PEqualNP.NotPremium.replaceByConst C.gates q.1 true) (List.ofFn x)).getD C.output false
      = (fl EV C.gates (List.ofFn x)).getD C.output false
    rw [set_same _ _ hq' true _ hvA]
