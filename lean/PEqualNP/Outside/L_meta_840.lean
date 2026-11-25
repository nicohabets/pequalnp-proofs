import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_840

-- A circuit with at most two gates computes, on the relevant sets, an OR of two AND terms
-- X Y ∨ P Q or a term Y (X ∨ P Q). A side that may only meet a maximal independent set
-- together with some other factors can be enlarged to the largest such set without losing a
-- true point; a finite check over the remaining two sides then shows that no such circuit is
-- false on every maximal independent set I and true on every I + u.

open PEqualNP.AndCount

def adjB (a b : Fin 7) : Bool :=
  decide ((a.val, b.val) ∈ ([(0, 4), (1, 5), (2, 6), (3, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∨ (b.val, a.val) ∈ ([(0, 4), (1, 5), (2, 6), (3, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)))

theorem adj_iff (G : SimpleGraph (Fin 7)) (hG : G.edgeSet = {s(0, 4), s(1, 5), s(2, 6), s(3, 6), s(4, 6), s(5, 6)}) (a b : Fin 7) :
    G.Adj a b ↔ adjB a b = true := by
  rw [← SimpleGraph.mem_edgeSet, hG]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  revert a b
  decide

def mis : List ℕ := [15, 30, 45, 60, 67]

def mt (s w : ℕ) : Bool := s &&& w != 0

theorem mt_iff (s w : ℕ) : mt s w = true ↔ ∃ i, s.testBit i = true ∧ w.testBit i = true := by
  unfold mt
  constructor
  · intro h
    have h' : s &&& w ≠ 0 := by simpa using h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h'
    rw [Nat.testBit_and, Bool.and_eq_true] at hi
    exact ⟨i, hi⟩
  · rintro ⟨i, h1, h2⟩
    have h3 : (s &&& w).testBit i = true := by rw [Nat.testBit_and, h1, h2]; rfl
    have h4 : s &&& w ≠ 0 := by
      intro h0; rw [h0, Nat.zero_testBit] at h3; exact Bool.false_ne_true h3
    simpa using h4

theorem bit_lt (s i : ℕ) (hs : s < 2 ^ 7) (h : s.testBit i = true) : i < 7 := by
  by_contra hc
  have := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hs (Nat.pow_le_pow_right (n := 2) (by norm_num) (show 7 ≤ i by omega)))
  rw [this] at h; exact Bool.false_ne_true h

def hit (xs : List ℕ) : List ℕ → ℕ
  | [] => 0
  | m :: ms => (if xs.all (fun x => mt x m) then m else 0) ||| hit xs ms

theorem hit_bit (xs : List ℕ) (i : ℕ) : ∀ ms : List ℕ, (hit xs ms).testBit i = true →
    ∃ m ∈ ms, xs.all (fun x => mt x m) = true ∧ m.testBit i = true
  | [] => by simp [hit]
  | m :: ms => by
    intro h
    simp only [hit, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · split_ifs at h with hc
      · exact ⟨m, List.mem_cons_self .., hc, h⟩
      · simp at h
    · obtain ⟨m', hm', h1, h2⟩ := hit_bit xs i ms h
      exact ⟨m', List.mem_cons_of_mem _ hm', h1, h2⟩

def MZ (xs : List ℕ) : ℕ := 127 ^^^ hit xs mis

theorem sub (xs : List ℕ) (s : ℕ) (hs : s < 2 ^ 7)
    (h : ∀ m ∈ mis, xs.all (fun x => mt x m) = true → mt s m = false) (w : ℕ) :
    mt s w = true → mt (MZ xs) w = true := by
  intro hw
  rw [mt_iff] at hw ⊢
  obtain ⟨i, h1, h2⟩ := hw
  refine ⟨i, ?_, h2⟩
  have hi := bit_lt s i hs h1
  have hh : (hit xs mis).testBit i = false := by
    by_contra hc
    obtain ⟨m, hm, hc1, hc2⟩ := hit_bit xs i mis (by simpa using hc)
    have h5 := h m hm hc1
    rw [(mt_iff s m).2 ⟨i, h1, hc2⟩] at h5
    simp at h5
  unfold MZ
  rw [Nat.testBit_xor, hh, show (127 : ℕ) = 2 ^ 7 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  simp [hi]

theorem mask_ex (S : Finset (Fin 7)) :
    ∃ m < 2 ^ 7, ∀ v : Fin 7, v ∈ S ↔ m.testBit v = true := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by norm_num, by simp⟩
  | insert a S ha ih =>
    obtain ⟨m, hm, h⟩ := ih
    refine ⟨m ||| 2 ^ (a : ℕ), Nat.or_lt_two_pow hm (Nat.pow_lt_pow_right (by norm_num) a.isLt), ?_⟩
    intro v
    rw [Finset.mem_insert, h v, Nat.testBit_or, Nat.testBit_two_pow, Fin.ext_iff, Bool.or_eq_true,
      decide_eq_true_iff]
    constructor
    · rintro (h1 | h1)
      · exact Or.inr h1.symm
      · exact Or.inl h1
    · rintro (h1 | h1)
      · exact Or.inr h1
      · exact Or.inl h1.symm

theorem meet (S U : Finset (Fin 7)) (s w : ℕ) (hs : ∀ v : Fin 7, v ∈ S ↔ s.testBit v = true)
    (hl : s < 2 ^ 7) (hw : ∀ v : Fin 7, v ∈ U ↔ w.testBit v = true) :
    decide (∃ v ∈ S, v ∈ U) = mt s w := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, mt_iff]
  constructor
  · rintro ⟨v, h1, h2⟩; exact ⟨v, (hs v).1 h1, (hw v).1 h2⟩
  · rintro ⟨i, h1, h2⟩
    exact ⟨⟨i, bit_lt s i hl h1⟩, (hs _).2 h1, (hw _).2 h2⟩

def Fo (α β o0 o1 xo x0 y0 x1 y1 : Bool) : Bool :=
  xo || (o0 && (x0 && y0)) || (o1 && ((x1 || (α && (x0 && y0))) && (y1 || (β && (x0 && y0)))))

theorem nf (C : AndCountCircuit 7) (hC : C.size < 3) : ∃ (α β o0 o1 : Bool)
    (O L0 R0 L1 R1 : Finset (Fin 7)), ∀ U, C.eval U = Fo α β o0 o1 (decide (∃ v ∈ O, v ∈ U))
      (decide (∃ v ∈ L0, v ∈ U)) (decide (∃ v ∈ R0, v ∈ U)) (decide (∃ v ∈ L1, v ∈ U))
      (decide (∃ v ∈ R1, v ∈ U)) := by
  obtain ⟨sz, lv, lg, rv, rg, ov, og⟩ := C
  simp only at hC
  rcases sz with _ | _ | _ | sz
  · refine ⟨false, false, false, false, ov, ∅, ∅, ∅, ∅, fun U => ?_⟩
    simp [AndCountCircuit.eval, Fo]
  · refine ⟨false, false, decide (0 ∈ og), false, ov, lv 0, rv 0, ∅, ∅, fun U => ?_⟩
    simp [AndCountCircuit.eval, AndCountCircuit.gateVal, AndCountCircuit.gateValFuel,
      AndCountCircuit.sideTrue, Fin.exists_fin_one, Fo]
  · refine ⟨decide (0 ∈ lg 1), decide (0 ∈ rg 1), decide (0 ∈ og), decide (1 ∈ og), ov, lv 0, rv 0,
      lv 1, rv 1, fun U => ?_⟩
    simp [AndCountCircuit.eval, AndCountCircuit.gateVal, AndCountCircuit.gateValFuel,
      AndCountCircuit.sideTrue, Fin.exists_fin_two, Fo, Bool.or_assoc]
  · omega

def cov (f : ℕ → Bool) : Bool :=
  mis.all (fun m => (List.range 7).all (fun u => m.testBit u || f (m ||| 2 ^ u)))

def F1 (x0 y0 x1 y1 w : ℕ) : Bool := (mt x0 w && mt y0 w) || (mt x1 w && mt y1 w)

def F2 (y x p q w : ℕ) : Bool := mt y w && (mt x w || (mt p w && mt q w))

theorem chk1_0 : ∀ a < 128, 0 ≤ a → ∀ b < 128, cov (fun w => F1 a (MZ [a]) b (MZ [b]) w) = false := by
  decide +kernel

theorem chk2_0 : ∀ a < 128, 0 ≤ a → ∀ b < 128, cov (fun w => F2 a (MZ [a]) b (MZ [a, b]) w) = false := by
  decide +kernel

theorem cov_true (f : ℕ → Bool)
    (h : ∀ m ∈ mis, ∀ u < 7, m.testBit u = false → f (m ||| 2 ^ u) = true) :
    cov f = true := by
  simp only [cov, List.all_eq_true, List.mem_range, Bool.or_eq_true]
  intro m hm u hu
  cases hb : m.testBit u
  · exact Or.inr (h m hm u hu hb)
  · exact Or.inl rfl

theorem use1 (a b : ℕ) (ha : a < 128) (hb : b < 128)
    (h : ∀ m ∈ mis, ∀ u < 7, m.testBit u = false →
      F1 a (MZ [a]) b (MZ [b]) (m ||| 2 ^ u) = true) : False := by
  have h1 := cov_true _ h
  have h2 : cov (fun w => F1 a (MZ [a]) b (MZ [b]) w) = false := by
    exact chk1_0 a (by omega) (by omega) b hb
  rw [h1] at h2; simp at h2

theorem use2 (a b : ℕ) (ha : a < 128) (hb : b < 128)
    (h : ∀ m ∈ mis, ∀ u < 7, m.testBit u = false →
      F2 a (MZ [a]) b (MZ [a, b]) (m ||| 2 ^ u) = true) : False := by
  have h1 := cov_true _ h
  have h2 : cov (fun w => F2 a (MZ [a]) b (MZ [a, b]) w) = false := by
    exact chk2_0 a (by omega) (by omega) b hb
  rw [h1] at h2; simp at h2

def mset (m : ℕ) : Finset (Fin 7) := Finset.univ.filter (fun i => m.testBit i.val)

theorem misOK : ∀ m ∈ mis,
    (∀ v w : Fin 7, m.testBit v = true → m.testBit w = true → adjB v w = false) ∧
    (∀ u : Fin 7, m.testBit u = false → ∃ v : Fin 7, m.testBit v = true ∧ adjB u v = true) := by
  decide +kernel

theorem mz0 : MZ [] = 0 := by decide +kernel

theorem main (G : SimpleGraph (Fin 7)) (hG : G.edgeSet = {s(0, 4), s(1, 5), s(2, 6), s(3, 6), s(4, 6), s(5, 6)})
    (C : AndCountCircuit 7)
    (H : ∀ I : Finset (Fin 7), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
      C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) : 3 ≤ C.size := by
  by_contra hlt
  obtain ⟨α, β, o0, o1, O, L0, R0, L1, R1, he⟩ := nf C (by omega)
  obtain ⟨o, ho, hO⟩ := mask_ex O
  obtain ⟨l0, hl0, hL0⟩ := mask_ex L0
  obtain ⟨r0, hr0, hR0⟩ := mask_ex R0
  obtain ⟨l1, hl1, hL1⟩ := mask_ex L1
  obtain ⟨r1, hr1, hR1⟩ := mask_ex R1
  have ev : ∀ (U : Finset (Fin 7)) (w : ℕ), (∀ v : Fin 7, v ∈ U ↔ w.testBit v = true) →
      C.eval U = Fo α β o0 o1 (mt o w) (mt l0 w) (mt r0 w) (mt l1 w) (mt r1 w) := by
    intro U w hw
    rw [he U, meet O U o w hO ho hw, meet L0 U l0 w hL0 hl0 hw, meet R0 U r0 w hR0 hr0 hw,
      meet L1 U l1 w hL1 hl1 hw, meet R1 U r1 w hR1 hr1 hw]
  have hmem : ∀ m : ℕ, ∀ v : Fin 7, v ∈ mset m ↔ m.testBit v = true := by
    intro m v; simp [mset]
  have HI : ∀ m ∈ mis, C.eval (mset m) = false ∧
      ∀ u, u ∉ mset m → C.eval (insert u (mset m)) = true := by
    intro m hm
    obtain ⟨h1, h2⟩ := misOK m hm
    apply H
    · intro v hv w hw ha
      rw [adj_iff G hG, h1 v w ((hmem m v).1 hv) ((hmem m w).1 hw)] at ha
      exact Bool.false_ne_true ha
    · intro u hu
      have hu' : m.testBit u = false := by
        cases hb : m.testBit u
        · rfl
        · exact absurd ((hmem m u).2 hb) hu
      obtain ⟨v, hv, ha⟩ := h2 u hu'
      exact ⟨v, (hmem m v).2 hv, (adj_iff G hG u v).2 ha⟩
  have Z : ∀ m ∈ mis, Fo α β o0 o1 (mt o m) (mt l0 m) (mt r0 m) (mt l1 m) (mt r1 m) = false := by
    intro m hm
    rw [← ev (mset m) m (hmem m)]
    exact (HI m hm).1
  have Cv : ∀ m ∈ mis, ∀ u < 7, m.testBit u = false →
      Fo α β o0 o1 (mt o (m ||| 2 ^ u)) (mt l0 (m ||| 2 ^ u)) (mt r0 (m ||| 2 ^ u))
        (mt l1 (m ||| 2 ^ u)) (mt r1 (m ||| 2 ^ u)) = true := by
    intro m hm u hu hb
    have hw : ∀ v : Fin 7, v ∈ insert (⟨u, hu⟩ : Fin 7) (mset m) ↔
        (m ||| 2 ^ u).testBit v = true := by
      intro v
      rw [Finset.mem_insert, hmem m v, Nat.testBit_or, Nat.testBit_two_pow, Fin.ext_iff,
        Bool.or_eq_true, decide_eq_true_iff]
      constructor
      · rintro (h1 | h1)
        · exact Or.inr h1.symm
        · exact Or.inl h1
      · rintro (h1 | h1)
        · exact Or.inr h1
        · exact Or.inl h1.symm
    rw [← ev _ _ hw]
    apply (HI m hm).2
    rw [hmem m]; simpa using hb
  have hxo : ∀ w, mt o w = false := by
    intro w
    cases hc : mt o w
    · rfl
    · have h3 := sub [] o ho (fun m hm _ => by
        have h4 := Z m hm
        simp only [Fo, Bool.or_eq_false_iff] at h4
        exact h4.1.1) w hc
      rw [mz0] at h3
      simp [mt] at h3
  clear he HI ev
  cases o1 <;> cases α <;> cases β <;> cases o0
  ·
    exact use1 0 0 (by norm_num) (by norm_num) (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w
      simp only [Fo, F1] at h ⊢
      revert h h' ; generalize mt (MZ [0]) w = P; generalize mt (MZ [0]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    have s0 := sub [l0] r0 hr0 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    exact use1 l0 0 hl0 (by norm_num) (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w; have s0w := s0 w
      simp only [Fo, F1] at h ⊢
      revert h h' s0w; generalize mt (MZ [l0]) w = P; generalize mt (MZ [0]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    exact use1 0 0 (by norm_num) (by norm_num) (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w
      simp only [Fo, F1] at h ⊢
      revert h h' ; generalize mt (MZ [0]) w = P; generalize mt (MZ [0]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    have s0 := sub [l0] r0 hr0 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    exact use1 l0 0 hl0 (by norm_num) (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w; have s0w := s0 w
      simp only [Fo, F1] at h ⊢
      revert h h' s0w; generalize mt (MZ [l0]) w = P; generalize mt (MZ [0]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    exact use1 0 0 (by norm_num) (by norm_num) (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w
      simp only [Fo, F1] at h ⊢
      revert h h' ; generalize mt (MZ [0]) w = P; generalize mt (MZ [0]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    have s0 := sub [l0] r0 hr0 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    exact use1 l0 0 hl0 (by norm_num) (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w; have s0w := s0 w
      simp only [Fo, F1] at h ⊢
      revert h h' s0w; generalize mt (MZ [l0]) w = P; generalize mt (MZ [0]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    exact use1 0 0 (by norm_num) (by norm_num) (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w
      simp only [Fo, F1] at h ⊢
      revert h h' ; generalize mt (MZ [0]) w = P; generalize mt (MZ [0]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    have s0 := sub [l0] r0 hr0 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    exact use1 l0 0 hl0 (by norm_num) (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w; have s0w := s0 w
      simp only [Fo, F1] at h ⊢
      revert h h' s0w; generalize mt (MZ [l0]) w = P; generalize mt (MZ [0]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    have s0 := sub [l1] r1 hr1 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    exact use1 l0 l1 hl0 hl1 (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w; have s0w := s0 w
      simp only [Fo, F1] at h ⊢
      revert h h' s0w; generalize mt (MZ [l0]) w = P; generalize mt (MZ [l1]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    have s0 := sub [l1] r1 hr1 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    have s1 := sub [l0] r0 hr0 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    exact use1 l0 l1 hl0 hl1 (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w; have s0w := s0 w; have s1w := s1 w
      simp only [Fo, F1] at h ⊢
      revert h h' s0w s1w; generalize mt (MZ [l0]) w = P; generalize mt (MZ [l1]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    have s0 := sub [l1] r1 hr1 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    have s1 := sub [l1, l0] r0 hr0 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    exact use2 l1 l0 hl1 hl0 (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w; have s0w := s0 w; have s1w := s1 w
      simp only [Fo, F2] at h ⊢
      revert h h' s0w s1w; generalize mt (MZ [l1]) w = P; generalize mt (MZ [l1, l0]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    have s0 := sub [l1] r1 hr1 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    have s1 := sub [l0] r0 hr0 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    exact use1 l0 l1 hl0 hl1 (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w; have s0w := s0 w; have s1w := s1 w
      simp only [Fo, F1] at h ⊢
      revert h h' s0w s1w; generalize mt (MZ [l0]) w = P; generalize mt (MZ [l1]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    have s0 := sub [r1] l1 hl1 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    have s1 := sub [r1, l0] r0 hr0 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    exact use2 r1 l0 hr1 hl0 (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w; have s0w := s0 w; have s1w := s1 w
      simp only [Fo, F2] at h ⊢
      revert h h' s0w s1w; generalize mt (MZ [r1]) w = P; generalize mt (MZ [r1, l0]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    have s0 := sub [l1] r1 hr1 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    have s1 := sub [l0] r0 hr0 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    exact use1 l0 l1 hl0 hl1 (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w; have s0w := s0 w; have s1w := s1 w
      simp only [Fo, F1] at h ⊢
      revert h h' s0w s1w; generalize mt (MZ [l0]) w = P; generalize mt (MZ [l1]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    have s0 := sub [l1] r1 hr1 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    have s1 := sub [l0] r0 hr0 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    exact use1 l0 l1 hl0 hl1 (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w; have s0w := s0 w; have s1w := s1 w
      simp only [Fo, F1] at h ⊢
      revert h h' s0w s1w; generalize mt (MZ [l0]) w = P; generalize mt (MZ [l1]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)
  ·
    have s0 := sub [l1] r1 hr1 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    have s1 := sub [l0] r0 hr0 (fun m hm hc => by
      have h := Z m hm
      have h' := hxo m
      simp only [Fo, List.all_cons, List.all_nil, Bool.and_true] at h hc
      revert h h' hc; generalize mt o m = A; generalize mt l0 m = B; generalize mt r0 m = C; generalize mt l1 m = D; generalize mt r1 m = E; revert A B C D E; decide)
    exact use1 l0 l1 hl0 hl1 (fun m hm u hu hb => by
      have h := Cv m hm u hu hb
      generalize m ||| 2 ^ u = w at h
      have h' := hxo w; have s0w := s0 w; have s1w := s1 w
      simp only [Fo, F1] at h ⊢
      revert h h' s0w s1w; generalize mt (MZ [l0]) w = P; generalize mt (MZ [l1]) w = Q; generalize mt o w = A; generalize mt l0 w = B
      generalize mt r0 w = C; generalize mt l1 w = D; generalize mt r1 w = E; generalize mt 0 w = Z0
      revert A B C D E P Q Z0; decide)

end PEqualNP.Outside.L_meta_840

theorem PEqualNP.Outside.L_meta_840 : ∀ G : SimpleGraph (Fin 7), G.edgeSet = {s(0, 4), s(1, 5), s(2, 6), s(3, 6), s(4, 6), s(5, 6)} → ∀ C : PEqualNP.AndCount.AndCountCircuit 7, C.WellFormed → (∀ I : Finset (Fin 7), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) → 3 ≤ C.size :=
  fun G hG C _ H => PEqualNP.Outside.L_meta_840.main G hG C H
