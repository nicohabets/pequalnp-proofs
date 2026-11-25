import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5585

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Truth tables as bit vectors: wire tables of depth at most d lie in lvl d, and the target is
-- not in lvl (bound - 1). The bit lemmas read_bit and read_wire and the shape of gate_ok follow
-- the merged proof of L-meta-139 (PEqualNP/Outside/L_meta_139.lean, by Lewis Watson).
abbrev T := BitVec 16

def ins : List T := [0xaaaa, 0xcccc, 0xf0f0, 0xff00, 0x5555, 0x3333, 0x0f0f, 0x00ff]

def target : T := 0x6996

def bit (k : Fin 16) (z : T) : Bool := z[k.val]

def nxtRaw (L : List T) : List T :=
  L ++ 0 :: (-1) :: L.flatMap (fun a => L.flatMap fun b => [a &&& b, a ||| b])

def nxt (L : List T) : List T := (nxtRaw L).eraseDups

def lvl : ℕ → List T
  | 0 => 0 :: ins
  | d + 1 => nxt (lvl d)

theorem mem_nxt (L : List T) (z : T) :
    z ∈ nxt L ↔ z ∈ L ∨ z = 0 ∨ z = -1 ∨ ∃ a ∈ L, ∃ b ∈ L, z = a &&& b ∨ z = a ||| b := by
  simp only [nxt, nxtRaw, List.mem_eraseDups, List.mem_append, List.mem_cons, List.mem_flatMap,
    List.not_mem_nil, or_false]

theorem mem_raw (L : List T) (z : T) : z ∈ nxtRaw L ↔ z ∈ nxt L := by
  simp only [nxt, List.mem_eraseDups]

theorem rep_getD (n i : ℕ) : (List.replicate n 0).getD i 0 = 0 := by
  by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, h]

theorem lvl_succ {d : ℕ} {z : T} (h : z ∈ lvl d) : z ∈ lvl (d + 1) :=
  (mem_nxt _ _).2 (Or.inl h)

theorem lvl_mono {a b : ℕ} {z : T} (hab : a ≤ b) (h : z ∈ lvl a) : z ∈ lvl b := by
  induction hab with
  | refl => exact h
  | step _ ih => exact lvl_succ ih

theorem read_bit (w : List T) (i : ℕ) (k : Fin 16) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

theorem read_wire (w : List T) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstep (d : List ℕ) (g : Gate) : List ℕ :=
  d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1]

def Good (w : List T) (dp : List ℕ) : Prop :=
  w.length = dp.length ∧ ∀ i, w.getD i 0 ∈ lvl (dp.getD i 0)

theorem zero_mem (d : ℕ) : (0 : T) ∈ lvl d :=
  lvl_mono (Nat.zero_le d) (by simp [lvl])

theorem good_snoc {w : List T} {dp : List ℕ} (hG : Good w dp) (z : T) (d : ℕ) (hz : z ∈ lvl d) :
    Good (w ++ [z]) (dp ++ [d]) := by
  refine ⟨by simp [hG.1], fun i => ?_⟩
  have hl := hG.1
  rcases Nat.lt_trichotomy i w.length with h | h | h
  · have e1 : (w ++ [z]).getD i 0 = w.getD i 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    have e2 : (dp ++ [d]).getD i 0 = dp.getD i 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hl ▸ h)]
    rw [e1, e2]; exact hG.2 i
  · have e1 : (w ++ [z]).getD i 0 = z := by
      subst h; simp [List.getD_eq_getElem?_getD]
    have e2 : (dp ++ [d]).getD i 0 = d := by
      rw [h, hl]; simp [List.getD_eq_getElem?_getD]
    rw [e1, e2]; exact hz
  · have e1 : (w ++ [z]).getD i 0 = 0 := by
      rw [List.getD_eq_default]; simp; omega
    rw [e1]; exact zero_mem _

theorem gate_ok (w : List T) (dp : List ℕ) (hG : Good w dp) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ z, (∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k)) ∧ Good (w ++ [z]) (dstep dp g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    have h1 : ((-1 : T)) ∈ lvl (0 + 1) := (mem_nxt _ _).2 (Or.inr (Or.inr (Or.inl rfl)))
    rcases hop with rfl | rfl
    · exact ⟨-1, by simp [step, GateOp.eval, bit]; decide, good_snoc hG _ _ h1⟩
    · exact ⟨0, by simp [step, GateOp.eval, bit], good_snoc hG _ _ (zero_mem _)⟩
  | cons i tail =>
    cases tail with
    | nil =>
      have h1 : w.getD i 0 ∈ lvl (max (dp.getD i 0) 0 + 1) := by
        rw [Nat.max_zero]; exact lvl_succ (hG.2 i)
      rcases hop with rfl | rfl
      · exact ⟨_, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval],
          good_snoc hG _ _ h1⟩
      · exact ⟨_, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval],
          good_snoc hG _ _ h1⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        have ha : w.getD i 0 ∈ lvl (max (dp.getD i 0) (max (dp.getD j 0) 0)) :=
          lvl_mono (Nat.le_max_left _ _) (hG.2 i)
        have hb : w.getD j 0 ∈ lvl (max (dp.getD i 0) (max (dp.getD j 0) 0)) :=
          lvl_mono (by omega) (hG.2 j)
        rcases hop with rfl | rfl
        · exact ⟨w.getD i 0 &&& w.getD j 0,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit],
            good_snoc hG _ _ ((mem_nxt _ _).2 (Or.inr (Or.inr (Or.inr ⟨_, ha, _, hb, Or.inl rfl⟩))))⟩
        · exact ⟨w.getD i 0 ||| w.getD j 0,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit],
            good_snoc hG _ _ ((mem_nxt _ _).2 (Or.inr (Or.inr (Or.inr ⟨_, ha, _, hb, Or.inr rfl⟩))))⟩

theorem run (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List T) (dp : List ℕ) (hG : Good w dp) :
    ∃ w', (∀ k, gs.foldl step (w.map (bit k)) = w'.map (bit k)) ∧ Good w' (gs.foldl dstep dp) := by
  induction gs generalizing w dp with
  | nil => exact ⟨w, fun _ => rfl, hG⟩
  | cons g gs ih =>
    obtain ⟨z, hz, hG'⟩ := gate_ok w dp hG g (hg g (by simp))
    obtain ⟨w', hw', hG''⟩ := ih (fun g' h => hg g' (by simp [h])) (w ++ [z]) (dstep dp g) hG'
    exact ⟨w', fun k => by simp only [List.foldl_cons, hz k]; exact hw' k, hG''⟩

def chk : Bool :=
  let L := nxtRaw (lvl 1)
  let sup := L.filter (fun a => a &&& target == target)
  let sub := L.filter (fun a => a ||| target == target)
  !L.contains target && (target != 0 && (target != -1 &&
  (sup.all (fun a => sup.all fun b => a &&& b != target) &&
   sub.all (fun a => sub.all fun b => a ||| b != target))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chk_true : chk = true := by decide +kernel

theorem target_out : target ∉ lvl (2 + 1) := by
  intro h
  have hc := chk_true
  simp only [chk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_filter,
    bne_iff_ne, ne_eq, beq_iff_eq, List.contains_eq_mem, decide_eq_false_iff_not] at hc
  obtain ⟨h0, h1, h2, h3, h4⟩ := hc
  rcases (mem_nxt _ _).1 h with h | h | h | ⟨a, ha, b, hb, h | h⟩
  · exact h0 ((mem_raw _ _).2 h)
  · exact h1 h
  · exact h2 h
  · refine h3 a ⟨(mem_raw _ _).2 ha, ?_⟩ b ⟨(mem_raw _ _).2 hb, ?_⟩ h.symm
    · rw [h, ← BitVec.and_assoc, BitVec.and_self]
    · rw [h, BitVec.and_comm a b, ← BitVec.and_assoc, BitVec.and_self]
  · refine h4 a ⟨(mem_raw _ _).2 ha, ?_⟩ b ⟨(mem_raw _ _).2 hb, ?_⟩ h.symm
    · rw [h, ← BitVec.or_assoc, BitVec.or_self]
    · rw [h, BitVec.or_comm a b, ← BitVec.or_assoc, BitVec.or_self]

def f (x : Fin 4 → Bool) : Bool := (fun a b : Bool => xor a b) ((fun u v : Bool => xor u v) (x 0) (x 1)) ((fun u v : Bool => xor u v) (x 2) (x 3))

def assignment (k : Fin 16) (i : Fin 4) : Bool := bit k (ins.getD i.val 0)

theorem lower (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 4 → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = f x) :
    4 ≤ C.depth (4 + 4) := by
  by_contra! hd
  have hG0 : Good ins (List.replicate (4 + 4) 0) := by
    refine ⟨by decide, fun i => ?_⟩
    have e := rep_getD (4 + 4) i
    rw [e]
    rcases read_wire ins i with h | h
    · rw [h]; exact zero_mem 0
    · exact List.mem_cons_of_mem _ h
  obtain ⟨w', hw', hG⟩ := run C.gates hm ins _ hG0
  have hmem := hG.2 C.output
  have hval : w'.getD C.output 0 = target := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have hi' : ∀ t, List.ofFn (assignment t) ++ List.ofFn (fun i => !assignment t i) =
        ins.map (bit t) := by decide
    have ht : ∀ t, f (assignment t) = bit t target := by decide
    have h1 := he (assignment ⟨i, hi⟩)
    rw [hi', ht] at h1
    have h2 : (C.gates.foldl step (ins.map (bit ⟨i, hi⟩))).getD C.output false =
        bit ⟨i, hi⟩ target := h1
    rw [hw', read_bit] at h2
    exact h2
  rw [hval] at hmem
  exact target_out (lvl_mono (show (C.gates.foldl dstep (List.replicate (4 + 4) 0)).getD
    C.output 0 ≤ 2 + 1 from Nat.lt_succ_iff.mp hd) hmem)

theorem upper : ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack (4 + 4) C ∧
    C.depth (4 + 4) ≤ 4 ∧
    ∀ x : Fin 4 → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = f x := by
  refine ⟨⟨[⟨.and, [0, 5]⟩, ⟨.and, [4, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [2, 7]⟩, ⟨.and, [6, 3]⟩, ⟨.or, [14, 15]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [10, 19]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [20, 21]⟩], 22⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    fin_cases hg <;> simp
  · decide
  · decide
  · decide +kernel

end PEqualNP.Outside.L_meta_5585

theorem PEqualNP.Outside.L_meta_5585 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 8 C ∧ C.depth 8 ≤ 4 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = (fun a b : Bool => xor a b) ((fun u v : Bool => xor u v) (x 0) (x 1)) ((fun u v : Bool => xor u v) (x 2) (x 3))) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 8 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = (fun a b : Bool => xor a b) ((fun u v : Bool => xor u v) (x 0) (x 1)) ((fun u v : Bool => xor u v) (x 2) (x 3))) → 4 ≤ C.depth 8) :=
  ⟨PEqualNP.Outside.L_meta_5585.upper, fun C hm _ he => PEqualNP.Outside.L_meta_5585.lower C hm he⟩
