import Mathlib
import PEqualNP.Defs

/-
Same family as the merged proofs of L-meta-8927 and L-meta-8245 by BastianMIllan (Petersen
graph minus a vertex); the wire fold follows his L-meta-8841 file.
Idea: give every wire the set of inputs it can depend on. Every input is essential, so the output
wire depends on all of them. Colour the inputs so that every dependency set is one colour; only an
AND/OR gate reading two wires can merge two colours, so there are at least n - 1 such gates, and
these are not NOT gates.
-/

namespace PEqualNP.Outside.L_meta_6320

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

def merging (g : Gate) : Bool := !isNot g.op && g.inputs.length == 2

def gD {n : ℕ} (Ds : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  if isNot g.op then Ds.getD (g.inputs.headD Ds.length) ∅
  else (g.inputs.map fun i => Ds.getD i ∅).foldr (· ∪ ·) ∅

def stepD {n : ℕ} (Ds : List (Finset (Fin n))) (g : Gate) : List (Finset (Fin n)) :=
  Ds ++ [gD Ds g]

theorem getD_snoc {α : Type} (W : List α) (v d : α) (i : ℕ) :
    (W ++ [v]).getD i d = if i < W.length then W.getD i d else if i = W.length then v else d := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp
  · rw [List.getD_eq_default]
    simp
    omega

def Agree {n : ℕ} (x y : Fin n → Bool) (Ds : List (Finset (Fin n))) (Wx Wy : List Bool) : Prop :=
  Ds.length = Wx.length ∧ Wx.length = Wy.length ∧
    ∀ w, (∀ i ∈ Ds.getD w ∅, x i = y i) → Wx.getD w false = Wy.getD w false

theorem mem_foldr_union {n : ℕ} (l : List (Finset (Fin n))) (s : Finset (Fin n)) (hs : s ∈ l) :
    s ⊆ l.foldr (· ∪ ·) ∅ := by
  induction l with
  | nil => simp at hs
  | cons a l ih =>
    rcases List.mem_cons.mp hs with rfl | h
    · exact Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

theorem agree_step {n : ℕ} (x y : Fin n → Bool) (Ds : List (Finset (Fin n))) (Wx Wy : List Bool)
    (g : Gate) (h : Agree x y Ds Wx Wy) :
    Agree x y (stepD Ds g) (step Wx g) (step Wy g) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp [stepD, step, h1], by simp [step, h2], fun w hw => ?_⟩
  simp only [stepD, step, getD_snoc] at hw ⊢
  rw [← h2]
  rw [← h1]
  split_ifs at hw ⊢ with ha hb
  · exact h3 w hw
  · by_cases hn : isNot g.op = true
    · have hop : g.op = GateOp.not := by
        cases h' : g.op <;> simp_all [isNot]
      rw [hop]
      simp only [GateOp.eval]
      cases hin : g.inputs with
      | nil => simp
      | cons j l =>
        simp only [List.map_cons, List.headD_cons]
        congr 1
        apply h3 j
        intro i hi
        apply hw i
        show i ∈ gD Ds g
        simp only [gD, hn, ite_true, hin, List.headD_cons]
        exact hi
    · have hv : ∀ j ∈ g.inputs, Wx.getD j false = Wy.getD j false := by
        intro j hj
        apply h3 j
        intro i hi
        apply hw i
        show i ∈ gD Ds g
        simp only [gD, hn, Bool.false_eq_true, ite_false]
        exact mem_foldr_union _ _ (List.mem_map.mpr ⟨j, hj, rfl⟩) hi
      have : (g.inputs.map fun i => Wx.getD i false) = (g.inputs.map fun i => Wy.getD i false) :=
        List.map_congr_left hv
      rw [this]
  · rfl

theorem agree_fold {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (Ds : List (Finset (Fin n))) (Wx Wy : List Bool), Agree x y Ds Wx Wy →
      Agree x y (gs.foldl stepD Ds) (gs.foldl step Wx) (gs.foldl step Wy) := by
  induction gs with
  | nil => intro Ds Wx Wy h; exact h
  | cons g gs ih =>
    intro Ds Wx Wy h
    exact ih _ _ _ (agree_step x y Ds Wx Wy g h)

def Mono {n : ℕ} (Ds : List (Finset (Fin n))) (c : Fin n → Fin n) : Prop :=
  ∀ w, ∀ i ∈ Ds.getD w ∅, ∀ j ∈ Ds.getD w ∅, c i = c j

theorem mono_snoc {n : ℕ} (Ds : List (Finset (Fin n))) (c : Fin n → Fin n) (s : Finset (Fin n))
    (h : Mono Ds c) (hs : ∀ i ∈ s, ∀ j ∈ s, c i = c j) : Mono (Ds ++ [s]) c := by
  intro w
  rw [getD_snoc]
  split_ifs
  · exact h w
  · exact hs
  · simp

theorem mono_recolor {n : ℕ} (Ds : List (Finset (Fin n))) (c : Fin n → Fin n) (α β : Fin n)
    (h : Mono Ds c) : Mono Ds (fun i => if c i = β then α else c i) := by
  intro w i hi j hj
  have := h w i hi j hj
  simp only [this]

theorem recolor_card {n : ℕ} (c : Fin n → Fin n) (α β : Fin n) :
    (Finset.univ.image c).card ≤ (Finset.univ.image (fun i => if c i = β then α else c i)).card + 1 := by
  have hsub : (Finset.univ.image c).erase β ⊆
      Finset.univ.image (fun i => if c i = β then α else c i) := by
    intro v hv
    obtain ⟨hvb, hv⟩ := Finset.mem_erase.mp hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp [hvb]⟩
  have := Finset.card_le_card hsub
  have h2 := Finset.pred_card_le_card_erase (s := Finset.univ.image c) (a := β)
  omega

theorem mono_single {n : ℕ} (Ds : List (Finset (Fin n))) (c : Fin n → Fin n) (h : Mono Ds c)
    (w : ℕ) : ∀ i ∈ Ds.getD w ∅, ∀ j ∈ Ds.getD w ∅, c i = c j := h w

theorem color_step {n : ℕ} (Ds : List (Finset (Fin n))) (c : Fin n → Fin n) (g : Gate)
    (hg : g.inputs.length ≤ 2) (h : Mono Ds c) :
    ∃ c' : Fin n → Fin n, Mono (stepD Ds g) c' ∧
      (Finset.univ.image c).card ≤ (Finset.univ.image c').card + (if merging g then 1 else 0) := by
  by_cases hn : isNot g.op = true
  · refine ⟨c, mono_snoc _ _ _ h ?_, by simp [merging, hn]⟩
    simp only [gD, hn, ite_true]
    exact h _
  · have hD : gD Ds g = (g.inputs.map fun i => Ds.getD i ∅).foldr (· ∪ ·) ∅ := by
      simp [gD, hn]
    match hin : g.inputs, hg with
    | [], _ =>
      refine ⟨c, mono_snoc _ _ _ h ?_, by simp⟩
      rw [hD, hin]; simp
    | [a], _ =>
      refine ⟨c, mono_snoc _ _ _ h ?_, by simp⟩
      rw [hD, hin]; simpa using h a
    | [a, b], _ =>
      have hS : gD Ds g = Ds.getD a ∅ ∪ Ds.getD b ∅ := by rw [hD, hin]; simp
      have hm : merging g = true := by simp [merging, hn, hin]
      by_cases ha : (Ds.getD a ∅).Nonempty
      · by_cases hb : (Ds.getD b ∅).Nonempty
        · obtain ⟨p, hp⟩ := ha
          obtain ⟨q, hq⟩ := hb
          refine ⟨fun i => if c i = c q then c p else c i, ?_, ?_⟩
          · refine mono_snoc _ _ _ (mono_recolor _ _ _ _ h) ?_
            rw [hS]
            have key : ∀ i ∈ Ds.getD a ∅ ∪ Ds.getD b ∅,
                (if c i = c q then c p else c i) = c p := by
              intro i hi
              rcases Finset.mem_union.mp hi with hi | hi
              · have := h a i hi p hp
                by_cases e : c i = c q
                · simp [e]
                · simp [e, this]
              · have := h b i hi q hq
                simp [this]
            intro i hi j hj
            rw [key i hi, key j hj]
          · rw [hm]; simpa using recolor_card c (c p) (c q)
        · rw [Finset.not_nonempty_iff_eq_empty] at hb
          refine ⟨c, mono_snoc _ _ _ h ?_, by simp⟩
          rw [hS, hb, Finset.union_empty]; exact h a
      · rw [Finset.not_nonempty_iff_eq_empty] at ha
        refine ⟨c, mono_snoc _ _ _ h ?_, by simp⟩
        rw [hS, ha, Finset.empty_union]; exact h b

theorem color_fold {n : ℕ} (gs : List Gate) (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ (Ds : List (Finset (Fin n))) (c : Fin n → Fin n), Mono Ds c →
      ∃ c' : Fin n → Fin n, Mono (gs.foldl stepD Ds) c' ∧
        (Finset.univ.image c).card ≤ (Finset.univ.image c').card + gs.countP merging := by
  induction gs with
  | nil => intro Ds c h; exact ⟨c, h, by simp⟩
  | cons g gs ih =>
    intro Ds c h
    obtain ⟨c1, h1, hc1⟩ := color_step Ds c g (hgs g List.mem_cons_self) h
    obtain ⟨c2, h2, hc2⟩ := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ c1 h1
    refine ⟨c2, h2, ?_⟩
    rw [List.countP_cons]
    split_ifs at hc1 <;> simp_all <;> omega

def D0 (n : ℕ) : List (Finset (Fin n)) := List.ofFn (fun i : Fin n => ({i} : Finset (Fin n))) ++ [∅]

theorem D0_getD (n : ℕ) (w : ℕ) :
    (D0 n).getD w ∅ = if h : w < n then {⟨w, h⟩} else ∅ := by
  unfold D0
  rw [getD_snoc]
  by_cases h1 : w < n
  · rw [if_pos (by simpa using h1), dif_pos h1, List.getD_eq_getElem _ _ (by simpa using h1)]
    simp
  · rw [if_neg (by simpa using h1), dif_neg h1]
    split_ifs <;> rfl

theorem agree0 {n : ℕ} (a b : Fin n) (x y : Fin n → Bool) (he : (x a || x b) = (y a || y b)) :
    Agree x y (D0 n) (List.ofFn x ++ [x a || x b]) (List.ofFn y ++ [y a || y b]) := by
  refine ⟨by simp [D0], by simp, fun w hw => ?_⟩
  rw [D0_getD] at hw
  rw [getD_snoc, getD_snoc]
  simp only [List.length_ofFn]
  split_ifs at hw ⊢ with h1 h2
  · rw [List.getD_eq_getElem _ _ (by simpa using h1), List.getD_eq_getElem _ _ (by simpa using h1)]
    simpa using hw ⟨w, h1⟩ (by simp)
  · exact he
  · rfl

theorem mono0 (n : ℕ) : Mono (D0 n) id := by
  intro w i hi j hj
  rw [D0_getD] at hi hj
  split_ifs at hi hj
  · simp at hi hj; simp [hi, hj]
  · simp at hi

theorem count_le (gs : List Gate) :
    gs.countP merging + (gs.filter fun g => isNot g.op).length ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [List.countP_cons, List.filter_cons]
    cases h : isNot g.op
    · simp only [merging, h, Bool.not_false, Bool.true_and, Bool.false_eq_true, if_false]
      split_ifs <;> simp <;> omega
    · simp only [merging, h, Bool.not_true, Bool.false_and, if_true, List.length_cons]
      simp; omega

theorem notCount_eq (gs : List Gate) (o : ℕ) :
    PEqualNP.NotBracket.notCount ⟨gs, o⟩ = (gs.filter fun g => isNot g.op).length := by
  unfold PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases h : g.op <;> simp [isNot]

theorem main (n : ℕ) (a b : Fin n) (C : Circuit) (f : (Fin n → Bool) → Bool)
    (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      (x a || x b) = (y a || y b) ∧ f x ≠ f y)
    (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x ++ [x a || x b]) = f x) :
    n + PEqualNP.NotBracket.notCount C ≤ C.size + 1 := by
  obtain ⟨gs, o⟩ := C
  rw [notCount_eq]
  have hcnt := count_le gs
  have hlen : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g hg => (hF g hg).2
  obtain ⟨c, hc, hcard⟩ := color_fold gs hlen (D0 n) id (mono0 n)
  have himg : (Finset.univ.image (id : Fin n → Fin n)).card = n := by simp
  have hall : ∀ i : Fin n, i ∈ (gs.foldl stepD (D0 n)).getD o ∅ := by
    intro i
    by_contra hi
    obtain ⟨x, y, hxy, he, hne⟩ := hess i
    have hA := (agree_fold x y gs _ _ _ (agree0 a b x y he)).2.2 o (by
      intro j hj
      apply hxy j
      rintro rfl
      exact hi hj)
    apply hne
    rw [← hC x, ← hC y]
    exact hA
  have hone : (Finset.univ.image c).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro u hu v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact hc o i (hall i) j (hall j)
  simp only [Circuit.size]
  omega

end PEqualNP.Outside.L_meta_6320

theorem PEqualNP.Outside.L_meta_6320 : ∀ (x1 : ℕ) (x2 x3 : Fin x1) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : (Fin x1 → Bool) → Bool), PEqualNP.MetaComplexity.FanInTwo x4 → (∀ (x7 : Fin x1), ∃ (x8 : Fin x1 → Bool) (x9 : Fin x1 → Bool), (∀ (x10 : Fin x1), x10 ≠ x7 → x8 x10 = x9 x10) ∧ (x8 x2 || x8 x3) = (x9 x2 || x9 x3) ∧ x5 x8 ≠ x5 x9) → (∀ (x8 : Fin x1 → Bool), x4.eval (List.ofFn x8 ++ [x8 x2 || x8 x3]) = x5 x8) → x1 + PEqualNP.NotBracket.notCount x4 ≤ x4.size + (1 : ℕ) := by
  intro n a b C f hF hess hC
  exact PEqualNP.Outside.L_meta_6320.main n a b C f hF hess hC
