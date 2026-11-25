import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5588

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Truth tables as bit vectors: wire tables of depth at most d lie in lvl d, and the target is
-- not in lvl 3 (the lists L1, SUP, SUB are checked by the kernel). The bit lemmas read_bit and read_wire and the shape of gate_ok follow
-- the merged proof of L-meta-139 (PEqualNP/Outside/L_meta_139.lean, by Lewis Watson).
abbrev T := BitVec 64

def ins : List T := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f, 0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]

def target : T := 0xf9f9f9f9f90000f9

def bit (k : Fin 64) (z : T) : Bool := z[k.val]

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

theorem read_bit (w : List T) (i : ℕ) (k : Fin 64) :
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

def L1 : List T := [0x0000000000000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f, 0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff, 0xffffffffffffffff, 0x8888888888888888, 0xeeeeeeeeeeeeeeee, 0xa0a0a0a0a0a0a0a0, 0xfafafafafafafafa, 0xaa00aa00aa00aa00, 0xffaaffaaffaaffaa, 0xaaaa0000aaaa0000, 0xffffaaaaffffaaaa, 0xaaaaaaaa00000000, 0xffffffffaaaaaaaa, 0x2222222222222222, 0xbbbbbbbbbbbbbbbb, 0x0a0a0a0a0a0a0a0a, 0xafafafafafafafaf, 0x00aa00aa00aa00aa, 0xaaffaaffaaffaaff, 0x0000aaaa0000aaaa, 0xaaaaffffaaaaffff, 0x00000000aaaaaaaa, 0xaaaaaaaaffffffff, 0xc0c0c0c0c0c0c0c0, 0xfcfcfcfcfcfcfcfc, 0xcc00cc00cc00cc00, 0xffccffccffccffcc, 0xcccc0000cccc0000, 0xffffccccffffcccc, 0xcccccccc00000000, 0xffffffffcccccccc, 0x4444444444444444, 0xdddddddddddddddd, 0x0c0c0c0c0c0c0c0c, 0xcfcfcfcfcfcfcfcf, 0x00cc00cc00cc00cc, 0xccffccffccffccff, 0x0000cccc0000cccc, 0xccccffffccccffff, 0x00000000cccccccc, 0xccccccccffffffff, 0xf000f000f000f000, 0xfff0fff0fff0fff0, 0xf0f00000f0f00000, 0xfffff0f0fffff0f0, 0xf0f0f0f000000000, 0xfffffffff0f0f0f0, 0x5050505050505050, 0xf5f5f5f5f5f5f5f5, 0x3030303030303030, 0xf3f3f3f3f3f3f3f3, 0x00f000f000f000f0, 0xf0fff0fff0fff0ff, 0x0000f0f00000f0f0, 0xf0f0fffff0f0ffff, 0x00000000f0f0f0f0, 0xf0f0f0f0ffffffff, 0xff000000ff000000, 0xffffff00ffffff00, 0xff00ff0000000000, 0xffffffffff00ff00, 0x5500550055005500, 0xff55ff55ff55ff55, 0x3300330033003300, 0xff33ff33ff33ff33, 0x0f000f000f000f00, 0xff0fff0fff0fff0f, 0x0000ff000000ff00, 0xff00ffffff00ffff, 0x00000000ff00ff00, 0xff00ff00ffffffff, 0xffff000000000000, 0xffffffffffff0000, 0x5555000055550000, 0xffff5555ffff5555, 0x3333000033330000, 0xffff3333ffff3333, 0x0f0f00000f0f0000, 0xffff0f0fffff0f0f, 0x00ff000000ff0000, 0xffff00ffffff00ff, 0x00000000ffff0000, 0xffff0000ffffffff, 0x5555555500000000, 0xffffffff55555555, 0x3333333300000000, 0xffffffff33333333, 0x0f0f0f0f00000000, 0xffffffff0f0f0f0f, 0x00ff00ff00000000, 0xffffffff00ff00ff, 0x0000ffff00000000, 0xffffffff0000ffff, 0x1111111111111111, 0x7777777777777777, 0x0505050505050505, 0x5f5f5f5f5f5f5f5f, 0x0055005500550055, 0x55ff55ff55ff55ff, 0x0000555500005555, 0x5555ffff5555ffff, 0x0000000055555555, 0x55555555ffffffff, 0x0303030303030303, 0x3f3f3f3f3f3f3f3f, 0x0033003300330033, 0x33ff33ff33ff33ff, 0x0000333300003333, 0x3333ffff3333ffff, 0x0000000033333333, 0x33333333ffffffff, 0x000f000f000f000f, 0x0fff0fff0fff0fff, 0x00000f0f00000f0f, 0x0f0fffff0f0fffff, 0x000000000f0f0f0f, 0x0f0f0f0fffffffff, 0x000000ff000000ff, 0x00ffffff00ffffff, 0x0000000000ff00ff, 0x00ff00ffffffffff, 0x000000000000ffff, 0x0000ffffffffffff]

def SUP : List T := [0xffffffffffffffff, 0xfbfbfbfbfbfbfbfb, 0xfdfdfdfdfdfdfdfd, 0xffffffffff00ffff, 0xffffffffffff00ff, 0xfffbfffbfffbfffb, 0xfffffbfbfffffbfb, 0xfffffffffbfbfbfb, 0xfbfffbfffbfffbff, 0xfbfbfffffbfbffff, 0xfbfbfbfbffffffff, 0xffffffffffaaffff, 0xffffffffffffaaff, 0xfffdfffdfffdfffd, 0xfffffdfdfffffdfd, 0xfffffffffdfdfdfd, 0xfdfffdfffdfffdff, 0xfdfdfffffdfdffff, 0xfdfdfdfdffffffff, 0xffffffffffccffff, 0xffffffffffffccff, 0xfffffffffff0ffff, 0xfffffffffffff0ff, 0xffffffffff55ffff, 0xffffffffff33ffff, 0xffffffffff0fffff, 0xffffffffffff55ff, 0xffffffffffff33ff, 0xffffffffffff0fff]

def SUB : List T := [0x0000000000000000, 0xf0f0f0f000000000, 0x8888888800000000, 0xa0a0a0a000000000, 0xc0c0c0c000000000, 0xf0000000f0000000, 0xf000f00000000000, 0xf0f0000000000000, 0x5050505000000000, 0x3030303000000000, 0x00f000f000000000, 0x0000f0f000000000, 0x000000f0000000f0, 0x1111111100000000, 0x8080808000000000, 0x8800000088000000, 0x8800880000000000, 0x8888000000000000, 0x0808080800000000, 0x0088008800000000, 0x0000888800000000, 0x0000008800000088, 0xe0e0e0e000000000, 0xa0000000a0000000, 0xa000a00000000000, 0xa0a0000000000000, 0x2020202000000000, 0x00a000a000000000, 0x0000a0a000000000, 0x000000a0000000a0, 0xc8c8c8c800000000, 0xf0a0f0a000000000, 0xf0f0a0a000000000, 0xa8a8a8a800000000, 0xb0b0b0b000000000, 0xa0f0a0f000000000, 0xa0a0f0f000000000, 0xc0000000c0000000, 0xc000c00000000000, 0xc0c0000000000000, 0x4040404000000000, 0x00c000c000000000, 0x0000c0c000000000, 0x000000c0000000c0, 0xf0c0f0c000000000, 0xf0f0c0c000000000, 0xd0d0d0d000000000, 0xc0f0c0f000000000, 0xc0c0f0f000000000, 0xf000000000000000, 0xf000f000f0000000, 0x5000000050000000, 0x3000000030000000, 0x00000000f0000000, 0x5000500000000000, 0x3000300000000000, 0x0000f00000000000, 0xf0f00000f0000000, 0x5050000000000000, 0x3030000000000000, 0x00f0000000000000, 0xf0f0f00000000000, 0xf050f05000000000, 0xf030f03000000000, 0xf000f0f000000000, 0xf0f0505000000000, 0xf0f0303000000000, 0xf0f000f000000000, 0x1010101000000000, 0x7070707000000000, 0x0050005000000000, 0x50f050f000000000, 0x0000505000000000, 0x5050f0f000000000, 0x0030003000000000, 0x30f030f000000000, 0x0000303000000000, 0x3030f0f000000000, 0x000000f000000000, 0x00f0f0f000000000, 0x0000005000000050, 0x3131313100000000, 0x0000003000000030, 0x5151515100000000, 0x00f000f0000000f0, 0x00000000000000f0, 0x0000f0f0000000f0, 0x1100000011000000, 0x1100110000000000, 0x1111000000000000, 0x0101010100000000, 0x0011001100000000, 0x0000111100000000, 0x0000001100000011]

def chkA : Bool := (nxtRaw (lvl 0)).all (fun z => L1.contains z)

def chkB : Bool := (nxtRaw L1).all (fun z => z != target &&
  (((z &&& target) != target || SUP.contains z) && ((z ||| target) != target || SUB.contains z)))

def chkC : Bool := target != 0 && (target != -1 &&
  (SUP.all (fun a => SUP.all fun b => a &&& b != target) &&
   SUB.all (fun a => SUB.all fun b => a ||| b != target)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chkA_true : chkA = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chkB_true : chkB = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chkC_true : chkC = true := by decide +kernel

theorem lvl1_sub {z : T} (h : z ∈ lvl 1) : z ∈ L1 := by
  have hA := chkA_true
  simp only [chkA, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hA
  exact hA z ((mem_raw _ _).2 h)

theorem lvl2_raw {z : T} (h : z ∈ lvl 2) : z ∈ nxtRaw L1 := by
  refine (mem_raw _ _).2 ((mem_nxt _ _).2 ?_)
  rcases (mem_nxt _ _).1 h with h | h | h | ⟨a, ha, b, hb, h⟩
  · exact Or.inl (lvl1_sub h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨a, lvl1_sub ha, b, lvl1_sub hb, h⟩))

theorem rawB {z : T} (h : z ∈ nxtRaw L1) :
    z ≠ target ∧ (z &&& target = target → z ∈ SUP) ∧ (z ||| target = target → z ∈ SUB) := by
  have hB := chkB_true
  simp only [chkB, List.all_eq_true] at hB
  have hz := hB z h
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_eq_mem,
    decide_eq_true_eq] at hz
  exact ⟨hz.1, fun e => hz.2.1.resolve_left (fun n => n e), fun e => hz.2.2.resolve_left (fun n => n e)⟩

theorem target_out : target ∉ lvl 3 := by
  intro h
  have hC := chkC_true
  simp only [chkC, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hC
  obtain ⟨h1, h2, h3, h4⟩ := hC
  rcases (mem_nxt _ _).1 h with h | h | h | ⟨a, ha, b, hb, h | h⟩
  · exact (rawB (lvl2_raw h)).1 rfl
  · exact h1 h
  · exact h2 h
  · refine h3 a ((rawB (lvl2_raw ha)).2.1 ?_) b ((rawB (lvl2_raw hb)).2.1 ?_) h.symm
    · rw [h, ← BitVec.and_assoc, BitVec.and_self]
    · rw [h, BitVec.and_comm a b, ← BitVec.and_assoc, BitVec.and_self]
  · refine h4 a ((rawB (lvl2_raw ha)).2.2 ?_) b ((rawB (lvl2_raw hb)).2.2 ?_) h.symm
    · rw [h, ← BitVec.or_assoc, BitVec.or_self]
    · rw [h, BitVec.or_comm a b, ← BitVec.or_assoc, BitVec.or_self]

def f (x : Fin 6 → Bool) : Bool := (fun a b : Bool => !a && !b) ((fun u v w : Bool => !w && ((u || v) && (!u || !v))) (x 0) (x 1) (x 2)) ((fun u v w : Bool => !w && ((u || v) && (!u || !v))) (x 3) (x 4) (x 5))

def assignment (k : Fin 64) (i : Fin 6) : Bool := bit k (ins.getD i.val 0)

theorem lower (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = f x) :
    4 ≤ C.depth (6 + 6) := by
  by_contra! hd
  have hG0 : Good ins (List.replicate (6 + 6) 0) := by
    refine ⟨by decide, fun i => ?_⟩
    have e := rep_getD (6 + 6) i
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
  exact target_out (lvl_mono (show (C.gates.foldl dstep (List.replicate (6 + 6) 0)).getD
    C.output 0 ≤ 3 from Nat.lt_succ_iff.mp hd) hmem)

theorem upper : ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack (6 + 6) C ∧
    C.depth (6 + 6) ≤ 4 ∧
    ∀ x : Fin 6 → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = f x := by
  refine ⟨⟨[⟨.and, [0, 1]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [14, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [18, 5]⟩, ⟨.and, [15, 19]⟩], 20⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    fin_cases hg <;> simp
  · decide
  · decide
  · decide +kernel

end PEqualNP.Outside.L_meta_5588

theorem PEqualNP.Outside.L_meta_5588 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 12 C ∧ C.depth 12 ≤ 4 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = (fun a b : Bool => !a && !b) ((fun u v w : Bool => !w && ((u || v) && (!u || !v))) (x 0) (x 1) (x 2)) ((fun u v w : Bool => !w && ((u || v) && (!u || !v))) (x 3) (x 4) (x 5))) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 12 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = (fun a b : Bool => !a && !b) ((fun u v w : Bool => !w && ((u || v) && (!u || !v))) (x 0) (x 1) (x 2)) ((fun u v w : Bool => !w && ((u || v) && (!u || !v))) (x 3) (x 4) (x 5))) → 4 ≤ C.depth 12) :=
  ⟨PEqualNP.Outside.L_meta_5588.upper, fun C hm _ he => PEqualNP.Outside.L_meta_5588.lower C hm he⟩
