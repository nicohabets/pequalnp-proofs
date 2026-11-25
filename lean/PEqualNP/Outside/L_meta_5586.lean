import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5586

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Truth tables as bit vectors: wire tables of depth at most d lie in lvl d, and the target is
-- not in lvl 3 (the lists L1, SUP, SUB are checked by the kernel). The bit lemmas read_bit and read_wire and the shape of gate_ok follow
-- the merged proof of L-meta-139 (PEqualNP/Outside/L_meta_139.lean, by Lewis Watson).
abbrev T := BitVec 64

def ins : List T := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f, 0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]

def target : T := 0x9009000000009009

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

def SUP : List T := [0xffffffffffffffff, 0xbbbbbbbbbbbbbbbb, 0xdddddddddddddddd, 0xf0fff0fff0fff0ff, 0xff0fff0fff0fff0f, 0xffff0000ffffffff, 0xffffffff0000ffff, 0xfbfbfbfbfbfbfbfb, 0xfafffafffafffaff, 0xffbbffbbffbbffbb, 0xffafffafffafffaf, 0xffffbbbbffffbbbb, 0xffffaaaaffffffff, 0xffffffffbbbbbbbb, 0xffffffffaaaaffff, 0xbfbfbfbfbfbfbfbf, 0xbbffbbffbbffbbff, 0xbbbbffffbbbbffff, 0xbbbbbbbbffffffff, 0xfdfdfdfdfdfdfdfd, 0xfcfffcfffcfffcff, 0xffddffddffddffdd, 0xffcfffcfffcfffcf, 0xffffddddffffdddd, 0xffffccccffffffff, 0xffffffffdddddddd, 0xffffffffccccffff, 0xdfdfdfdfdfdfdfdf, 0xddffddffddffddff, 0xddddffffddddffff, 0xddddddddffffffff, 0xfffff0fffffff0ff, 0xfffff0f0ffffffff, 0xfffffffff0fff0ff, 0xfffffffff0f0ffff, 0xf5fff5fff5fff5ff, 0xf3fff3fff3fff3ff, 0xf0fffffff0ffffff, 0xf0fff0ffffffffff, 0xffffff0fffffff0f, 0xffffff00ffffffff, 0xffffffffff0fff0f, 0xffffffffff00ffff, 0xff5fff5fff5fff5f, 0xff3fff3fff3fff3f, 0xff0fffffff0fffff, 0xff0fff0fffffffff, 0xffff5555ffffffff, 0xffff3333ffffffff, 0xffff0f0fffffffff, 0xffff00ffffffffff, 0xffffffff5555ffff, 0xffffffff3333ffff, 0xffffffff0f0fffff, 0xffffffff00ffffff, 0xf8fff8fff8fff8ff, 0xff8fff8fff8fff8f, 0xffff8888ffffffff, 0xffffffff8888ffff, 0x9999999999999999, 0xfefffefffefffeff, 0xffefffefffefffef, 0xffffeeeeffffffff, 0xffffffffeeeeffff, 0xffffa0a0ffffffff, 0xffffffffa0a0ffff, 0xb3ffb3ffb3ffb3ff, 0xfffbfffbfffbfffb, 0xfffffbfbfffffbfb, 0xfffffafffffffaff, 0xfffffafaffffffff, 0xfffffffffbfbfbfb, 0xfffffffffafffaff, 0xfffffffffafaffff, 0xfafbfafbfafbfafb, 0xfbfffbfffbfffbff, 0xfbfbfffffbfbffff, 0xfbfbfbfbffffffff, 0xfafffffffaffffff, 0xfafffaffffffffff, 0xffffaa00ffffffff, 0xffffffffaa00ffff, 0xbf3fbf3fbf3fbf3f, 0xffffffbbffffffbb, 0xffffffafffffffaf, 0xffffffaaffffffff, 0xffffffffffbbffbb, 0xffffffffffafffaf, 0xffffffffffaaffff, 0xffabffabffabffab, 0xffbfffbfffbfffbf, 0xffbbffffffbbffff, 0xffbbffbbffffffff, 0xffafffffffafffff, 0xffafffafffffffff, 0xfafff0fffafff0ff, 0xffafff0fffafff0f, 0xbbbb3333ffffffff, 0xffffffffffffbbbb, 0xffffbfbfffffbfbf, 0xffffbbffffffbbff, 0xffffaaaaffffbbbb, 0xffffbbbbffffffff, 0xffffafafffffffff, 0xffffaaffffffffff, 0xfafffafff0fff0ff, 0xffafffafff0fff0f, 0xbbbbffff3333ffff, 0xffffffffbfbfbfbf, 0xffffffffbbffbbff, 0xffffffffaaaabbbb, 0xffffffffbbbbffff, 0xffffffffafafffff, 0xffffffffaaffffff, 0xf2fff2fff2fff2ff, 0xff2fff2fff2fff2f, 0xffff2222ffffffff, 0xffffffff2222ffff, 0xfbbbfbbbfbbbfbbb, 0xfbfbbbbbfbfbbbbb, 0xfbfbfbfbbbbbbbbb, 0xbbfbbbfbbbfbbbfb, 0xb0bbb0bbb0bbb0bb, 0xbbbbfbfbbbbbfbfb, 0xbbbbbbbbfbfbfbfb, 0xffbbbbbbffbbbbbb, 0xffbbffbbbbbbbbbb, 0xbfbbbfbbbfbbbfbb, 0xbb0bbb0bbb0bbb0b, 0xbbbbffbbbbbbffbb, 0xbbbbbbbbffbbffbb, 0xffffbbbbbbbbbbbb, 0xbfbfbbbbbfbfbbbb, 0xbbffbbbbbbffbbbb, 0xbbbbbbbbffffbbbb, 0xbbbb0000bbbbbbbb, 0xbfbfbfbfbbbbbbbb, 0xbbffbbffbbbbbbbb, 0xbbbbffffbbbbbbbb, 0xbbbbbbbb0000bbbb, 0xbbbfbbbfbbbfbbbf, 0xbfffbfffbfffbfff, 0xbbbbbfbfbbbbbfbf, 0xbfbfffffbfbfffff, 0xbbbbbbbbbfbfbfbf, 0xbfbfbfbfffffffff, 0xbbbbbbffbbbbbbff, 0xbbffffffbbffffff, 0xbbbbbbbbbbffbbff, 0xbbffbbffffffffff, 0xbbbbbbbbbbbbffff, 0xbbbbffffffffffff, 0xff3bff3bff3bff3b, 0xffff0a0affffffff, 0xffffffff0a0affff, 0xbfafbfafbfafbfaf, 0xf3fbf3fbf3fbf3fb, 0xffff00aaffffffff, 0xffffffff00aaffff, 0xbaffbaffbaffbaff, 0xf0fffafff0fffaff, 0xff0fffafff0fffaf, 0xffffffff3333bbbb, 0xbbbbffffaaaaffff, 0xf0fff0fffafffaff, 0xff0fff0fffafffaf, 0xffff3333ffffbbbb, 0xbbbbaaaaffffffff, 0xffffc0c0ffffffff, 0xffffffffc0c0ffff, 0xd5ffd5ffd5ffd5ff, 0xfffdfffdfffdfffd, 0xfffffdfdfffffdfd, 0xfffffcfffffffcff, 0xfffffcfcffffffff, 0xfffffffffdfdfdfd, 0xfffffffffcfffcff, 0xfffffffffcfcffff, 0xfcfdfcfdfcfdfcfd, 0xfdfffdfffdfffdff, 0xfdfdfffffdfdffff, 0xfdfdfdfdffffffff, 0xfcfffffffcffffff, 0xfcfffcffffffffff, 0xffffcc00ffffffff, 0xffffffffcc00ffff, 0xdf5fdf5fdf5fdf5f, 0xffffffddffffffdd, 0xffffffcfffffffcf, 0xffffffccffffffff, 0xffffffffffddffdd, 0xffffffffffcfffcf, 0xffffffffffccffff, 0xffcdffcdffcdffcd, 0xffdfffdfffdfffdf, 0xffddffffffddffff, 0xffddffddffffffff, 0xffcfffffffcfffff, 0xffcfffcfffffffff, 0xfcfff0fffcfff0ff, 0xffcfff0fffcfff0f, 0xdddd5555ffffffff, 0xffffffffffffdddd, 0xffffdfdfffffdfdf, 0xffffddffffffddff, 0xffffccccffffdddd, 0xffffddddffffffff, 0xffffcfcfffffffff, 0xffffccffffffffff, 0xfcfffcfff0fff0ff, 0xffcfffcfff0fff0f, 0xddddffff5555ffff, 0xffffffffdfdfdfdf, 0xffffffffddffddff, 0xffffffffccccdddd, 0xffffffffddddffff, 0xffffffffcfcfffff, 0xffffffffccffffff, 0xf4fff4fff4fff4ff, 0xff4fff4fff4fff4f, 0xffff4444ffffffff, 0xffffffff4444ffff, 0xfdddfdddfdddfddd, 0xfdfdddddfdfddddd, 0xfdfdfdfddddddddd, 0xddfdddfdddfdddfd, 0xd0ddd0ddd0ddd0dd, 0xddddfdfdddddfdfd, 0xddddddddfdfdfdfd, 0xffddddddffdddddd, 0xffddffdddddddddd, 0xdfdddfdddfdddfdd, 0xdd0ddd0ddd0ddd0d, 0xddddffddddddffdd, 0xddddddddffddffdd, 0xffffdddddddddddd, 0xdfdfdddddfdfdddd, 0xddffddddddffdddd, 0xddddddddffffdddd, 0xdddd0000dddddddd, 0xdfdfdfdfdddddddd, 0xddffddffdddddddd, 0xddddffffdddddddd, 0xdddddddd0000dddd, 0xdddfdddfdddfdddf, 0xdfffdfffdfffdfff, 0xdddddfdfdddddfdf, 0xdfdfffffdfdfffff, 0xdddddddddfdfdfdf, 0xdfdfdfdfffffffff, 0xddddddffddddddff, 0xddffffffddffffff, 0xddddddddddffddff, 0xddffddffffffffff, 0xddddddddddddffff, 0xddddffffffffffff, 0xff5dff5dff5dff5d, 0xffff0c0cffffffff, 0xffffffff0c0cffff, 0xdfcfdfcfdfcfdfcf, 0xf5fdf5fdf5fdf5fd, 0xffff00ccffffffff, 0xffffffff00ccffff, 0xdcffdcffdcffdcff, 0xf0fffcfff0fffcff, 0xff0fffcfff0fffcf, 0xffffffff5555dddd, 0xddddffffccccffff, 0xf0fff0fffcfffcff, 0xff0fff0fffcfffcf, 0xffff5555ffffdddd, 0xddddccccffffffff, 0xfffff000ffffffff, 0xfffffffff000ffff, 0xf00ff00ff00ff00f, 0xfffffff0ffffffff, 0xfffffffffff0ffff, 0xf0ff00ffffffffff, 0xfffffffffffff0ff, 0xfffff5fffffff5ff, 0xfffff5f5ffffffff, 0xfffff3fffffff3ff, 0xfffff3f3ffffffff, 0xfffff0f0fffff0ff, 0xfffff0ffffffffff, 0xf0ffffff00ffffff, 0xfffffffff5fff5ff, 0xfffffffff5f5ffff, 0xfffffffff3fff3ff, 0xfffffffff3f3ffff, 0xfffffffff0f0f0ff, 0xfffffffff0ffffff, 0xffff5050ffffffff, 0xffffffff5050ffff, 0xf7fff7fff7fff7ff, 0xf5fffffff5ffffff, 0xf5fff5ffffffffff, 0xffff3030ffffffff, 0xffffffff3030ffff, 0xf3fffffff3ffffff, 0xf3fff3ffffffffff, 0xffff00f0ffffffff, 0xffffffff00f0ffff, 0xfffff0fff0fff0ff, 0xf5fff0fff5fff0ff, 0xf3fff0fff3fff0ff, 0xf0fff0fffffff0ff, 0xf0ff0000f0fff0ff, 0xf5fff5fff0fff0ff, 0xf3fff3fff0fff0ff, 0xf0fffffff0fff0ff, 0xf0fff0ff0000f0ff, 0xf1fff1fff1fff1ff, 0xf0fff5fff0fff5ff, 0xf0fff0fff5fff5ff, 0xf0fff3fff0fff3ff, 0xf0fff0fff3fff3ff, 0xf0fff0fff0ffffff, 0xf0ffffffffffffff, 0xffffffff00fff0ff, 0xf0fffffff0f0ffff, 0xffff00fffffff0ff, 0xf0fff0f0ffffffff, 0xff0f0f0fffffffff, 0xffffffffffffff0f, 0xffffff5fffffff5f, 0xffffff55ffffffff, 0xffffff3fffffff3f, 0xffffff33ffffffff, 0xffffff00ffffff0f, 0xffffff0fffffffff, 0xff0fffff0f0fffff, 0xffffffffff5fff5f, 0xffffffffff55ffff, 0xffffffffff3fff3f, 0xffffffffff33ffff, 0xffffffffff00ff0f, 0xffffffffff0fffff, 0xffff5500ffffffff, 0xffffffff5500ffff, 0xff7fff7fff7fff7f, 0xff5fffffff5fffff, 0xff5fff5fffffffff, 0xffff3300ffffffff, 0xffffffff3300ffff, 0xff3fffffff3fffff, 0xff3fff3fffffffff, 0xffff0f00ffffffff, 0xffffffff0f00ffff, 0xffffff0fff0fff0f, 0xff5fff0fff5fff0f, 0xff3fff0fff3fff0f, 0xff0fff0fffffff0f, 0xff0f0000ff0fff0f, 0xff5fff5fff0fff0f, 0xff3fff3fff0fff0f, 0xff0fffffff0fff0f, 0xff0fff0f0000ff0f, 0xff1fff1fff1fff1f, 0xff0fff5fff0fff5f, 0xff0fff0fff5fff5f, 0xff0fff3fff0fff3f, 0xff0fff0fff3fff3f, 0xff0fff0fff0fffff, 0xff0fffffffffffff, 0xffffffff0f0fff0f, 0xff0fffffff00ffff, 0xffff0f0fffffff0f, 0xff0fff00ffffffff, 0xffff00000000ffff, 0xffff7777ffffffff, 0xffff5f5fffffffff, 0xffff55ffffffffff, 0xffff3f3fffffffff, 0xffff33ffffffffff, 0xffff0fffffffffff, 0xffff1111ffffffff, 0xffff0505ffffffff, 0xffff0055ffffffff, 0xffff0303ffffffff, 0xffff0033ffffffff, 0xffff000fffffffff, 0xffffffff7777ffff, 0xffffffff5f5fffff, 0xffffffff55ffffff, 0xffffffff3f3fffff, 0xffffffff33ffffff, 0xffffffff0fffffff, 0xffffffff1111ffff, 0xffffffff0505ffff, 0xffffffff0055ffff, 0xffffffff0303ffff, 0xffffffff0033ffff, 0xffffffff000fffff]

def SUB : List T := [0x0000000000000000]

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

def f (x : Fin 6 → Bool) : Bool := (fun a b c : Bool => !a && (!b && !c)) ((fun u v : Bool => xor u v) (x 0) (x 1)) ((fun u v : Bool => xor u v) (x 2) (x 3)) ((fun u v : Bool => xor u v) (x 4) (x 5))

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
  refine ⟨⟨[⟨.and, [0, 1]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [17, 20]⟩, ⟨.and, [14, 21]⟩], 22⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    fin_cases hg <;> simp
  · decide
  · decide
  · decide +kernel

end PEqualNP.Outside.L_meta_5586

theorem PEqualNP.Outside.L_meta_5586 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 12 C ∧ C.depth 12 ≤ 4 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = (fun a b c : Bool => !a && (!b && !c)) ((fun u v : Bool => xor u v) (x 0) (x 1)) ((fun u v : Bool => xor u v) (x 2) (x 3)) ((fun u v : Bool => xor u v) (x 4) (x 5))) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 12 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = (fun a b c : Bool => !a && (!b && !c)) ((fun u v : Bool => xor u v) (x 0) (x 1)) ((fun u v : Bool => xor u v) (x 2) (x 3)) ((fun u v : Bool => xor u v) (x 4) (x 5))) → 4 ≤ C.depth 12) :=
  ⟨PEqualNP.Outside.L_meta_5586.upper, fun C hm _ he => PEqualNP.Outside.L_meta_5586.lower C hm he⟩
