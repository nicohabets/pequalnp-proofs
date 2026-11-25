import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1318

/-! The linearity law of L-meta-1317 (proved again here with the same argument, its lemmas copied; the degree-0 wire induction comes from L-meta-1313): at line-degree at most 1 the value at both lines on is the value at no line on or at one line on. For y0 AND y1 the first is true and the others false. -/

open PEqualNP.CircuitLowerBounds

theorem ld_snoc (gs : List Gate) (g : Gate) (o o' n : ℕ) (marked : Finset ℕ) :
    Circuit.lineDegrees ⟨gs ++ [g], o⟩ n marked =
      Circuit.lineDegrees ⟨gs, o'⟩ n marked ++
        [g.lineDegree (Circuit.lineDegrees ⟨gs, o'⟩ n marked)] := by
  simp [Circuit.lineDegrees, List.foldl_append]

theorem ld_length (gs : List Gate) (o n : ℕ) (marked : Finset ℕ) :
    (Circuit.lineDegrees ⟨gs, o⟩ n marked).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.lineDegrees]
  | append_singleton gs g ih => rw [ld_snoc _ _ _ o]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [this]

theorem w_snoc (gs : List Gate) (g : Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g], o⟩ x = Circuit.wires ⟨gs, o'⟩ x ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, o'⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem w_length (gs : List Gate) (o : ℕ) (x : List Bool) :
    (Circuit.wires ⟨gs, o⟩ x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih => rw [w_snoc _ _ _ o]; simp [ih]; omega

theorem le_foldr_max (l : List ℕ) (x : ℕ) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih hx) (le_max_right _ _)

theorem inputs_zero (g : Gate) (d : List ℕ) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : g.lineDegree d = 0) : ∀ j ∈ g.inputs, d.getD j 0 = 0 := by
  intro j hj
  have hm : d.getD j 0 ∈ g.inputs.map fun i => d.getD i 0 := List.mem_map.2 ⟨j, hj, rfl⟩
  unfold Gate.lineDegree at h
  rcases hop with hop | hop
  · rw [if_pos hop] at h
    exact (List.sum_eq_zero_iff.1 h) _ hm
  · rw [if_neg (by rw [hop]; simp)] at h
    have := le_foldr_max _ _ hm
    omega

theorem key (gs : List Gate) (o n : ℕ) (marked : Finset ℕ) (x x' : List Bool)
    (hx : x.length = n) (hx' : x'.length = n)
    (hagree : ∀ i < n, i ∉ marked → x.getD i false = x'.getD i false)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (Circuit.lineDegrees ⟨gs, o⟩ n marked).getD i 0 = 0 →
      (Circuit.wires ⟨gs, o⟩ x).getD i false = (Circuit.wires ⟨gs, o⟩ x').getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    simp only [Circuit.lineDegrees, Circuit.wires, List.foldl_nil] at hi ⊢
    by_cases hin : i < n
    · rw [List.getD_eq_getElem _ _ (by simp; omega)] at hi
      simp only [List.getElem_map, List.getElem_range] at hi
      exact hagree i hin (by intro hm; simp [hm] at hi)
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hmono g' (by simp [hg']))
    intro i hi
    rw [ld_snoc _ _ _ o, getD_snoc, ld_length] at hi
    rw [w_snoc _ _ _ o, w_snoc _ _ _ o, getD_snoc, getD_snoc, w_length, w_length, hx, hx']
    split_ifs at hi ⊢ with h1 h2
    · exact ih' i hi
    · have hz := inputs_zero g _ (hmono g (by simp)) hi
      congr 1
      exact List.map_congr_left (fun j hj => ih' j (hz j hj))
    · rfl

theorem uniq (L : List ℕ) (f : ℕ → ℕ) (h : (L.map f).sum ≤ 1) :
    ∀ a ∈ L, ∀ b ∈ L, f a ≠ 0 → f b ≠ 0 → a = b := by
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.map_cons, List.sum_cons] at h
    intro a ha b hb fa fb
    have hs : ∀ y ∈ L, f y ≤ (L.map f).sum := fun y hy =>
      List.le_sum_of_mem (List.mem_map_of_mem hy)
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · have := hs b hb'; rw [ha'] at fa; omega
    · have := hs a ha'; rw [hb'] at fb; omega
    · exact ih (by omega) a ha' b hb' fa fb

theorem gate_step (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (d : List ℕ)
    (wx wp : ℕ → Bool) (we : ℕ → ℕ → Bool) (Good : ℕ → Prop)
    (ih : ∀ i, d.getD i 0 ≤ 1 → wx i = true → wp i = true ∨ ∃ j, Good j ∧ we j i = true)
    (z1 : ∀ i, d.getD i 0 = 0 → wx i = wp i)
    (z2 : ∀ j, Good j → ∀ i, d.getD i 0 = 0 → wx i = we j i)
    (hd : g.lineDegree d ≤ 1)
    (hv : g.op.eval (g.inputs.map wx) = true) :
    g.op.eval (g.inputs.map wp) = true ∨ ∃ j, Good j ∧ g.op.eval (g.inputs.map (we j)) = true := by
  unfold Gate.lineDegree at hd
  rcases hop with hop | hop
  · rw [if_pos hop] at hd
    rw [hop] at hv ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂] at hv ⊢
    have hle : ∀ a ∈ g.inputs, d.getD a 0 ≤ 1 := fun a ha =>
      le_trans (List.le_sum_of_mem (List.mem_map_of_mem (f := fun i => d.getD i 0) ha)) hd
    have hu := uniq g.inputs (fun i => d.getD i 0) hd
    by_cases hall : ∀ a ∈ g.inputs, d.getD a 0 = 0
    · left; intro a ha; rw [← z1 a (hall a ha)]; exact hv a ha
    · push_neg at hall
      obtain ⟨b, hb, hb0⟩ := hall
      rcases ih b (hle b hb) (hv b hb) with h | ⟨j, hj, hq⟩
      · left; intro a ha
        by_cases ha0 : d.getD a 0 = 0
        · rw [← z1 a ha0]; exact hv a ha
        · rw [hu a ha b hb ha0 hb0]; exact h
      · right; refine ⟨j, hj, ?_⟩; intro a ha
        by_cases ha0 : d.getD a 0 = 0
        · rw [← z2 j hj a ha0]; exact hv a ha
        · rw [hu a ha b hb ha0 hb0]; exact hq
  · rw [if_neg (by rw [hop]; simp)] at hd
    rw [hop] at hv ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hv ⊢
    obtain ⟨_, ⟨a, ha, rfl⟩, hva⟩ := hv
    have hm : d.getD a 0 ∈ g.inputs.map fun i => d.getD i 0 := List.mem_map.2 ⟨a, ha, rfl⟩
    rcases ih a (le_trans (le_foldr_max _ _ hm) hd) hva with h | ⟨j, hj, hq⟩
    · left; exact ⟨_, ⟨a, ha, rfl⟩, h⟩
    · right; exact ⟨j, hj, _, ⟨a, ha, rfl⟩, hq⟩

theorem lin (gs : List Gate) (o n : ℕ) (marked : Finset ℕ) (x p : List Bool) (E : ℕ → List Bool)
    (hx : x.length = n) (hp : p.length = n) (hE : ∀ j, (E j).length = n)
    (hpa : ∀ i < n, i ∉ marked → x.getD i false = p.getD i false)
    (hEa : ∀ j, j ∈ marked → ∀ i < n, i ∉ marked → x.getD i false = (E j).getD i false)
    (hEj : ∀ j < n, j ∈ marked → (E j).getD j false = true)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (Circuit.lineDegrees ⟨gs, o⟩ n marked).getD i 0 ≤ 1 →
      (Circuit.wires ⟨gs, o⟩ x).getD i false = true →
      (Circuit.wires ⟨gs, o⟩ p).getD i false = true ∨
        ∃ j < n, j ∈ marked ∧ x.getD j false = true ∧
          (Circuit.wires ⟨gs, o⟩ (E j)).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i _ hv
    simp only [Circuit.wires, List.foldl_nil] at hv ⊢
    by_cases hin : i < n
    · by_cases hm : i ∈ marked
      · right; exact ⟨i, hin, hm, hv, hEj i hin hm⟩
      · left; rw [← hpa i hin hm]; exact hv
    · rw [List.getD_eq_default _ _ (by omega)] at hv
      simp at hv
  | append_singleton gs g ih =>
    have hm' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hmono g' (by simp [hg'])
    have ih' := ih hm'
    have kp := key gs o n marked x p hx hp hpa hm'
    have ke := fun j (hj : j ∈ marked) => key gs o n marked x (E j) hx (hE j) (hEa j hj) hm'
    intro i hd hv
    rw [ld_snoc _ _ _ o, getD_snoc, ld_length] at hd
    rw [w_snoc _ _ _ o, getD_snoc, w_length, hx] at hv
    by_cases h1 : i < n + gs.length
    · rw [if_pos h1] at hd hv
      rcases ih' i hd hv with h | ⟨j, hj1, hj2, hj3, hq⟩
      · left; rw [w_snoc _ _ _ o, getD_snoc, w_length, hp, if_pos h1]; exact h
      · right; refine ⟨j, hj1, hj2, hj3, ?_⟩
        rw [w_snoc _ _ _ o, getD_snoc, w_length, hE, if_pos h1]; exact hq
    · rw [if_neg h1] at hd hv
      by_cases h2 : i = n + gs.length
      · rw [if_pos h2] at hd hv
        rcases gate_step g (hmono g (by simp)) _
            (fun i => (Circuit.wires ⟨gs, o⟩ x).getD i false)
            (fun i => (Circuit.wires ⟨gs, o⟩ p).getD i false)
            (fun j i => (Circuit.wires ⟨gs, o⟩ (E j)).getD i false)
            (fun j => j < n ∧ j ∈ marked ∧ x.getD j false = true)
            (fun i hd hv => by
              rcases ih' i hd hv with h | ⟨j, a, b, c, q⟩
              exacts [Or.inl h, Or.inr ⟨j, ⟨a, b, c⟩, q⟩])
            kp (fun j hj => ke j hj.2.1) hd hv with h | ⟨j, ⟨hj1, hj2, hj3⟩, hq⟩
        · left; rw [w_snoc _ _ _ o, getD_snoc, w_length, hp, if_neg h1, if_pos h2]; exact h
        · right; refine ⟨j, hj1, hj2, hj3, ?_⟩
          rw [w_snoc _ _ _ o, getD_snoc, w_length, hE, if_neg h1, if_pos h2]; exact hq
      · rw [if_neg h2] at hv; simp at hv

theorem mono_w (gs : List Gate) (o : ℕ) (x y : List Bool) (hxy : x.length = y.length)
    (hle : ∀ i, x.getD i false = true → y.getD i false = true)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (Circuit.wires ⟨gs, o⟩ x).getD i false = true →
      (Circuit.wires ⟨gs, o⟩ y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa [Circuit.wires] using hle
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hmono g' (by simp [hg']))
    intro i hv
    rw [w_snoc _ _ _ o, getD_snoc, w_length, hxy] at hv
    rw [w_snoc _ _ _ o, getD_snoc, w_length]
    split_ifs at hv ⊢ with h1 h2
    · exact ih' i hv
    · rcases hmono g (by simp) with hop | hop
      · rw [hop] at hv ⊢
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂] at hv ⊢
        intro a ha; exact ih' a (hv a ha)
      · rw [hop] at hv ⊢
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hv ⊢
        obtain ⟨_, ⟨a, ha, rfl⟩, hva⟩ := hv
        exact ⟨_, ⟨a, ha, rfl⟩, ih' a hva⟩

theorem lin_iff :
∀ (n : ℕ) (marked : Finset ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree n marked C 1 → ∀ z : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C z = true ↔ (PEqualNP.MetaComplexity.circuitFun n C (fun i => if i.val ∈ marked then false else z i) = true ∨ ∃ j : Fin n, j.val ∈ marked ∧ z j = true ∧ PEqualNP.MetaComplexity.circuitFun n C (fun i => if i = j then true else if i.val ∈ marked then false else z i) = true) := by
  intro n marked C hC hD z
  obtain ⟨gs, o⟩ := C
  have hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  have h1 : (Circuit.lineDegrees ⟨gs, o⟩ n marked).getD o 0 ≤ 1 := hD
  unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval
  have hEf : ∀ j : Fin n, (fun i : Fin n => if i = j then true else if i.val ∈ marked then false
      else z i) = (fun i : Fin n => if i.val = j.val then true else if i.val ∈ marked then false
      else z i) := by
    intro j; funext i; simp [Fin.ext_iff]
  constructor
  · intro hv
    rcases lin gs o n marked (List.ofFn z)
        (List.ofFn (fun i : Fin n => if i.val ∈ marked then false else z i))
        (fun j => List.ofFn (fun i : Fin n => if i.val = j then true else if i.val ∈ marked then false
          else z i))
        (by simp) (by simp) (fun j => by simp)
        (by
          intro i hi hm
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
          simp [hm])
        (by
          intro j hj i hi hm
          have hij : i ≠ j := by rintro rfl; exact hm hj
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
          simp [hm, hij])
        (by
          intro j hj _
          rw [List.getD_eq_getElem _ _ (by simp; omega)]
          simp)
        hmono o h1 hv with h | ⟨j, hj, hjm, hjx, hq⟩
    · left; exact h
    · right
      refine ⟨⟨j, hj⟩, hjm, ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ (by simp; omega)] at hjx
        simpa using hjx
      · rw [hEf]; exact hq
  · rintro (h | ⟨j, _, hjz, hq⟩)
    · refine mono_w gs o _ _ (by simp) ?_ hmono o h
      intro i hi
      by_cases hin : i < n
      · rw [List.getD_eq_getElem _ _ (by simp; omega)] at hi ⊢
        simp only [List.getElem_ofFn] at hi ⊢
        split_ifs at hi
        exact hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        simp at hi
    · refine mono_w gs o _ _ (by simp) ?_ hmono o hq
      intro i hi
      by_cases hin : i < n
      · rw [List.getD_eq_getElem _ _ (by simp; omega)] at hi ⊢
        simp only [List.getElem_ofFn] at hi ⊢
        split_ifs at hi with ha hb
        · rw [ha]; exact hjz
        · exact hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        simp at hi

end PEqualNP.Outside.L_meta_1318

theorem PEqualNP.Outside.L_meta_1318 :
∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree 2 (Finset.Ico 0 2) C 1 → ¬ (∀ z : Fin 2 → Bool, PEqualNP.MetaComplexity.circuitFun 2 C z = (z 0 && z 1)) := by
  intro C hC hD hf
  have h := PEqualNP.Outside.L_meta_1318.lin_iff 2 (Finset.Ico 0 2) C hC hD (fun _ => true)
  simp only [hf] at h
  revert h
  decide
