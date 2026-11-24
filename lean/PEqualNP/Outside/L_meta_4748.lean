import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4748
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

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

theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem ev_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f g : ℕ → Bool) (h : ∀ i ∈ ins, f i = true → g i = true) :
    op.eval (ins.map f) = true → op.eval (ins.map g) = true := by
  rcases hop with h' | h' <;> rw [h']
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun H i hi => h i hi (H i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hi hv⟩

theorem app_mono (A A' B B' : List Bool) (hA : A.length = A'.length)
    (ha : ∀ i, A.getD i false = true → A'.getD i false = true)
    (hb : ∀ i, B.getD i false = true → B'.getD i false = true) :
    ∀ i, (A ++ B).getD i false = true → (A' ++ B').getD i false = true := by
  intro i
  by_cases hi : i < A.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hA ▸ hi)]; exact ha i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hA]
    exact hb _

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

def sg (n g a : ℕ) (gg : Gate) : Gate :=
  { op := gg.op, inputs := gg.inputs.map (fun i => if i = n + g then a else i) }

theorem redirect_same (n g a : ℕ) (gs : List Gate) (X : List Bool) (hX : X.length = n)
    (hrb : ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j) (ha : a < n + g)
    (heq : (wf gs X).getD (n + g) false = (wf gs X).getD a false) :
    ∀ m, m ≤ gs.length → wf ((gs.map (sg n g a)).take m) X = wf (gs.take m) X := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have hm' : m < gs.length := hm
    have t1 : (gs.map (sg n g a)).take (m + 1) = (gs.map (sg n g a)).take m ++ [sg n g a gs[m]] := by
      rw [List.take_succ_eq_append_getElem (by simpa using hm'), List.getElem_map]
    have t2 : gs.take (m + 1) = gs.take m ++ [gs[m]] := List.take_succ_eq_append_getElem hm'
    rw [t1, t2, wf_snoc, wf_snoc, ih (le_of_lt hm')]
    congr 2
    show gs[m].op.eval ((gs[m].inputs.map (fun i => if i = n + g then a else i)).map
        fun i => (wf (gs.take m) X).getD i false)
      = gs[m].op.eval (gs[m].inputs.map fun i => (wf (gs.take m) X).getD i false)
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    show (wf (gs.take m) X).getD (if i = n + g then a else i) false = (wf (gs.take m) X).getD i false
    split_ifs with h
    · have hi' := hrb m hm' i hi
      rw [h, ← wire_take gs X m a (by rw [hX]; omega) (le_of_lt hm'),
        ← wire_take gs X m (n + g) (by rw [hX]; omega) (le_of_lt hm')]
      exact heq.symm
    · rfl

theorem redirect_up (n g a : ℕ) (gs : List Gate) (X : List Bool) (hX : X.length = n)
    (hrb : ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j) (ha : a < n + g)
    (hao : ∀ gg ∈ gs, gg.op = GateOp.and ∨ gg.op = GateOp.or)
    (hga : (wf gs X).getD (n + g) false = true → (wf gs X).getD a false = true) :
    ∀ m, m ≤ gs.length → ∀ i, (wf (gs.take m) X).getD i false = true →
      (wf ((gs.map (sg n g a)).take m) X).getD i false = true := by
  intro m
  induction m with
  | zero => intro _ i h; exact h
  | succ m ih =>
    intro hm
    have hm' : m < gs.length := hm
    have ih' := ih (le_of_lt hm')
    have t1 : (gs.map (sg n g a)).take (m + 1) = (gs.map (sg n g a)).take m ++ [sg n g a gs[m]] := by
      rw [List.take_succ_eq_append_getElem (by simpa using hm'), List.getElem_map]
    have t2 : gs.take (m + 1) = gs.take m ++ [gs[m]] := List.take_succ_eq_append_getElem hm'
    rw [t1, t2, wf_snoc, wf_snoc]
    apply app_mono _ _ _ _ (by
      rw [wf_len, wf_len, List.length_take, List.length_take, List.length_map]) ih'
    intro j
    cases j with
    | succ j => intro h1; simp at h1
    | zero =>
      show gs[m].op.eval (gs[m].inputs.map fun i => (wf (gs.take m) X).getD i false) = true →
        gs[m].op.eval ((gs[m].inputs.map (fun i => if i = n + g then a else i)).map
          fun i => (wf ((gs.map (sg n g a)).take m) X).getD i false) = true
      rw [List.map_map]
      apply ev_mono gs[m].op (hao _ (List.getElem_mem hm')) gs[m].inputs
      intro i hi hp
      show (wf ((gs.map (sg n g a)).take m) X).getD (if i = n + g then a else i) false = true
      split_ifs with h
      · have hi' := hrb m hm' i hi
        apply ih'
        rw [← wire_take gs X m a (by rw [hX]; omega) (le_of_lt hm')]
        apply hga
        rw [wire_take gs X m (n + g) (by rw [hX]; omega) (le_of_lt hm'), ← h]
        exact hp
      · exact ih' i hp

theorem redirect_down (n g a : ℕ) (gs : List Gate) (X : List Bool) (hX : X.length = n)
    (hrb : ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j) (ha : a < n + g)
    (hao : ∀ gg ∈ gs, gg.op = GateOp.and ∨ gg.op = GateOp.or)
    (hga : (wf gs X).getD a false = true → (wf gs X).getD (n + g) false = true) :
    ∀ m, m ≤ gs.length → ∀ i, (wf ((gs.map (sg n g a)).take m) X).getD i false = true →
      (wf (gs.take m) X).getD i false = true := by
  intro m
  induction m with
  | zero => intro _ i h; exact h
  | succ m ih =>
    intro hm
    have hm' : m < gs.length := hm
    have ih' := ih (le_of_lt hm')
    have t1 : (gs.map (sg n g a)).take (m + 1) = (gs.map (sg n g a)).take m ++ [sg n g a gs[m]] := by
      rw [List.take_succ_eq_append_getElem (by simpa using hm'), List.getElem_map]
    have t2 : gs.take (m + 1) = gs.take m ++ [gs[m]] := List.take_succ_eq_append_getElem hm'
    rw [t1, t2, wf_snoc, wf_snoc]
    apply app_mono _ _ _ _ (by
      rw [wf_len, wf_len, List.length_take, List.length_take, List.length_map]) ih'
    intro j
    cases j with
    | succ j => intro h1; simp at h1
    | zero =>
      show gs[m].op.eval ((gs[m].inputs.map (fun i => if i = n + g then a else i)).map
          fun i => (wf ((gs.map (sg n g a)).take m) X).getD i false) = true →
        gs[m].op.eval (gs[m].inputs.map fun i => (wf (gs.take m) X).getD i false) = true
      rw [List.map_map]
      apply ev_mono gs[m].op (hao _ (List.getElem_mem hm')) gs[m].inputs
      intro i hi hp
      have hp' : (wf ((gs.map (sg n g a)).take m) X).getD (if i = n + g then a else i) false = true := hp
      split_ifs at hp' with h
      · have hi' := hrb m hm' i hi
        rw [h, ← wire_take gs X m (n + g) (by rw [hX]; omega) (le_of_lt hm')]
        apply hga
        rw [wire_take gs X m a (by rw [hX]; omega) (le_of_lt hm')]
        exact ih' a hp'
      · exact ih' i hp'

theorem gF_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (y : Fin n → Bool)
    (h : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = true) :
    ∃ u v, G.Adj u v ∧ y u = true ∧ y v = true := by
  unfold PEqualNP.MetaComplexity.NestedCover.graphFun at h
  simpa using h

theorem gF_of {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (y : Fin n → Bool)
    (u v : Fin n) (hadj : G.Adj u v) (hu : y u = true) (hv : y v = true) :
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = true := by
  unfold PEqualNP.MetaComplexity.NestedCover.graphFun
  rw [Bool.or_eq_true]
  right
  exact decide_eq_true ⟨u, v, hadj, hu, hv⟩

theorem mapIdx_const {α β : Type} (f : α → β) (l : List α) :
    l.mapIdx (fun _ a => f a) = l.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem redirect_F (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (j y : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hfun : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = true ↔
      ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)
    (hy : y < n + j)
    (hE : ∀ a b : Fin n, G.Adj a b →
      (wf C.gates (List.ofFn (fun i : Fin n => decide (i = a ∨ i = b)))).getD (n + j) false = true →
      (wf C.gates (List.ofFn (fun i : Fin n => decide (i = a ∨ i = b)))).getD y false = true)
    (hD : ∀ x : Fin n → Bool, (wf C.gates (List.ofFn x)).getD y false = true →
      ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) :
    ∀ x : Fin n → Bool,
      PEqualNP.MetaComplexity.circuitFun n (PEqualNP.FactorSubst.substReads C n j (fun _ => y)) x = true ↔
      ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true := by
  obtain ⟨hao, hrb, hlen2⟩ := hAO
  have hrb' : ∀ k (hk : k < C.gates.length), ∀ i ∈ C.gates[k].inputs, i < n + k :=
    fun k hk i hi => hrb k hk i (by rw [gateAt_eq C k hk]; exact hi)
  have hg : (PEqualNP.FactorSubst.substReads C n j (fun _ => y)).gates = C.gates.map (sg n j y) :=
    mapIdx_const (sg n j y) C.gates
  have hleg' : ∀ gg ∈ C.gates.map (sg n j y),
      (gg.op = GateOp.and ∨ gg.op = GateOp.or) ∧ gg.inputs.length ≤ 2 := by
    intro gg hgg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hgg
    refine ⟨hao g0 hg0, ?_⟩
    show (g0.inputs.map _).length ≤ 2
    rw [List.length_map]; exact le_of_eq (hlen2 g0 hg0)
  have e1 : (C.gates.map (sg n j y)).take C.gates.length = C.gates.map (sg n j y) :=
    List.take_of_length_le (by simp)
  have e2 : C.gates.take C.gates.length = C.gates := List.take_of_length_le (le_refl _)
  intro x
  show (wf (PEqualNP.FactorSubst.substReads C n j (fun _ => y)).gates (List.ofFn x)).getD C.output false
    = true ↔ _
  rw [hg]
  constructor
  · intro h'
    by_contra hno
    have h1 := redirect_down n j y C.gates (List.ofFn x) (by simp) hrb' hy hao
      (fun h2 => absurd (hD x h2) hno) C.gates.length (le_refl _) C.output
    rw [e1, e2] at h1
    exact hno ((hfun x).1 (h1 h'))
  · rintro ⟨a, b, hadj, ha, hb⟩
    have hpx : ∀ t : Fin n, (fun i : Fin n => decide (i = a ∨ i = b)) t = true → x t = true := by
      intro t ht
      rcases of_decide_eq_true ht with e | e
      · rw [e]; exact ha
      · rw [e]; exact hb
    apply mono2 _ hleg' _ _ (by simp) (ofFn_mono n _ x hpx)
    have hout : (wf C.gates (List.ofFn (fun i : Fin n => decide (i = a ∨ i = b)))).getD C.output false
        = true :=
      (hfun _).2 ⟨a, b, hadj, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
    have h1 := redirect_up n j y C.gates _ (by simp) hrb' hy hao (hE a b hadj)
      C.gates.length (le_refl _) C.output
    rw [e1, e2] at h1
    exact h1 hout

end PEqualNP.Outside.L_meta_4748

open PEqualNP.Outside.L_meta_4748 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4748 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (j y : ℕ),
  PEqualNP.TopForm.IsAO2 n C → j < C.gates.length →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)) →
  y < n + j →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD y false =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true ∧
        (C.wires (List.ofFn (fun i => decide (i = a ∨ i = b)))).getD (n + j) false = true)) →
  ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n (PEqualNP.FactorSubst.substReads C n j (fun _ => y)) x =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) := by
  intro n G _ C j y hAO hj hop hfun hy hyv x
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  apply redirect_F n G C j y hAO (fun x => by rw [hfun x, decide_eq_true_iff]) hy
  · intro a b hadj h
    show (C.wires (List.ofFn (fun i : Fin n => decide (i = a ∨ i = b)))).getD y false = true
    rw [hyv]
    exact decide_eq_true ⟨a, b, hadj, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl), h⟩
  · intro x hx
    have hx' : (C.wires (List.ofFn x)).getD y false = true := hx
    rw [hyv] at hx'
    obtain ⟨a, b, h1, h2, h3, _⟩ := of_decide_eq_true hx'
    exact ⟨a, b, h1, h2, h3⟩
