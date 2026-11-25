import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5451

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev T := BitVec 16

def ins4 : List T := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

def bit (k : Fin 16) (z : T) : Bool := z[k.val]

lemma read_bit (w : List T) (i : ℕ) (k : Fin 16) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

lemma read_wire (w : List T) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

lemma atom {ws : List T} {x : T} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x = true ∧ possible ws (~~~x) = true := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact ⟨Or.inr ⟨x, hx, Or.inl (Or.inl rfl)⟩, Or.inr ⟨x, hx, Or.inl (Or.inr rfl)⟩⟩

lemma neg1_eq_allOnes : (-1 : T) = BitVec.allOnes 16 := by decide
lemma zero_eq_bv0 : (0 : T) = 0#16 := rfl
lemma bv_zero_and (x : T) : (0 : T) &&& x = 0 := by rw [zero_eq_bv0, BitVec.zero_and]
lemma bv_and_zero (x : T) : x &&& (0 : T) = 0 := by rw [zero_eq_bv0, BitVec.and_zero]
lemma bv_zero_or (x : T) : (0 : T) ||| x = x := by rw [zero_eq_bv0, BitVec.zero_or]
lemma bv_or_zero (x : T) : x ||| (0 : T) = x := by rw [zero_eq_bv0, BitVec.or_zero]
lemma bv_neg1_and (x : T) : (-1 : T) &&& x = x := by rw [neg1_eq_allOnes, BitVec.allOnes_and]
lemma bv_and_neg1 (x : T) : x &&& (-1 : T) = x := by rw [neg1_eq_allOnes, BitVec.and_allOnes]
lemma bv_neg1_or (x : T) : (-1 : T) ||| x = -1 := by rw [neg1_eq_allOnes, BitVec.allOnes_or]
lemma bv_or_neg1 (x : T) : x ||| (-1 : T) = -1 := by rw [neg1_eq_allOnes, BitVec.or_allOnes]
lemma contains_false_iff (l : List T) (a : T) : l.contains a = false ↔ a ∉ l := by simp

lemma pair {ws : List T} {x y : T} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) = true ∧ possible ws (x ||| y) = true := by
  rcases hx with rfl | hx
  · rw [bv_zero_and, bv_zero_or]
    exact ⟨by simp [possible], (atom hy).1⟩
  rcases hy with rfl | hy
  · rw [bv_and_zero, bv_or_zero]
    exact ⟨by simp [possible], (atom (.inr hx)).1⟩
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact ⟨Or.inr ⟨x, hx, Or.inr ⟨y, hy, Or.inl rfl⟩⟩,
      Or.inr ⟨x, hx, Or.inr ⟨y, hy, Or.inr rfl⟩⟩⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma gate_table (w ws : List T) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z = true ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def safe (tgt : T) : ℕ → List T → Prop
  | 0, ws => ws.contains tgt = false
  | n + 1, ws => ∀ z, possible ws z = true → safe tgt n (z :: ws)

lemma absent {tgt : T} {n : ℕ} {ws : List T} (h : safe tgt n ws) : tgt ∉ ws := by
  induction n generalizing ws with
  | zero => simpa [safe] using h
  | succ n ih =>
    have ht := ih (h 0 (by simp [possible]))
    exact fun hm => ht (List.mem_cons_of_mem _ hm)

lemma exclude (tgt : T) (ht0 : tgt ≠ 0) (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w ws : List T) (hw : w ⊆ ws) (m : ℕ) (hm : gs.length ≤ m) (hs : safe tgt m ws)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k tgt) : False := by
  induction gs generalizing w ws m with
  | nil =>
    have hval : w.getD out 0 = tgt := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | ht
    · exact ht0 hz
    · exact absent hs (hw ht)
  | cons g gs ih =>
    cases m with
    | zero => simp at hm
    | succ m =>
      obtain ⟨z, hz, hstep⟩ := gate_table w ws hw g (hg g (by simp))
      apply ih (fun g' hg' => hg g' (by simp [hg'])) (w ++ [z]) (z :: ws) _ m
        (by simpa using hm) (hs z hz)
      · intro k
        simpa only [List.foldl_cons, hstep] using he k
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact List.mem_cons_of_mem _ (hw hx)
        · simp

lemma possible_mono {ws1 ws2 : List T} (hsub : ∀ x ∈ ws1, x = 0 ∨ x = -1 ∨ x ∈ ws2)
    {z : T} (hz : possible ws1 z = true) : possible ws2 z = true := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with (rfl | rfl) | ⟨u, hu, (rfl | rfl) | ⟨v, hv, rfl | rfl⟩⟩
  · simp [possible]
  · simp [possible]
  · rcases hsub z hu with rfl | rfl | hu2
    · simp [possible]
    · simp [possible]
    · exact (atom (.inr hu2)).1
  · rcases hsub u hu with rfl | rfl | hu2
    · simp [possible]
    · simp [possible]
    · exact (atom (.inr hu2)).2
  · rcases hsub u hu with rfl | rfl | hu2
    · rw [bv_zero_and]
      simp [possible]
    · rw [bv_neg1_and]
      rcases hsub v hv with rfl | rfl | hv2
      · simp [possible]
      · simp [possible]
      · exact (atom (.inr hv2)).1
    · rcases hsub v hv with rfl | rfl | hv2
      · rw [bv_and_zero]
        simp [possible]
      · rw [bv_and_neg1]
        exact (atom (.inr hu2)).1
      · exact (pair (.inr hu2) (.inr hv2)).1
  · rcases hsub u hu with rfl | rfl | hu2
    · rw [bv_zero_or]
      rcases hsub v hv with rfl | rfl | hv2
      · simp [possible]
      · simp [possible]
      · exact (atom (.inr hv2)).1
    · rw [bv_neg1_or]
      simp [possible]
    · rcases hsub v hv with rfl | rfl | hv2
      · rw [bv_or_zero]
        exact (atom (.inr hu2)).1
      · rw [bv_or_neg1]
        simp [possible]
      · exact (pair (.inr hu2) (.inr hv2)).2

lemma safe_mono {tgt : T} (ht0 : tgt ≠ 0) (ht1 : tgt ≠ -1) {n : ℕ} :
    ∀ {ws1 ws2 : List T}, (∀ x ∈ ws1, x = 0 ∨ x = -1 ∨ x ∈ ws2) →
      safe tgt n ws2 → safe tgt n ws1 := by
  induction n with
  | zero =>
    intro ws1 ws2 hsub hs
    simp only [safe, contains_false_iff] at hs ⊢
    intro hm
    rcases hsub tgt hm with h | h | h
    · exact ht0 h
    · exact ht1 h
    · exact hs h
  | succ n ih =>
    intro ws1 ws2 hsub hs z hz
    refine ih ?_ (hs z (possible_mono hsub hz))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inr (Or.inr List.mem_cons_self)
    · rcases hsub x hx with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))

def pairOps : List T → List T
  | [] => []
  | x :: xs => (~~~x) :: xs.flatMap (fun y => [x &&& y, x ||| y]) ++ pairOps xs

lemma pairOps_not {ws : List T} {x : T} (hx : x ∈ ws) : ~~~x ∈ pairOps ws := by
  induction ws with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [pairOps]
    · exact List.mem_append_right _ (ih hx)

lemma pairOps_bin {ws : List T} {x y : T} (hx : x ∈ ws) (hy : y ∈ ws) (hne : x ≠ y) :
    (x &&& y) ∈ pairOps ws ∧ (x ||| y) ∈ pairOps ws := by
  induction ws with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · exact (hne rfl).elim
    · simp only [pairOps, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap]
      exact ⟨Or.inr (Or.inl ⟨y, hy', by simp⟩), Or.inr (Or.inl ⟨y, hy', by simp⟩)⟩
    · simp only [pairOps, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap]
      rw [BitVec.and_comm, BitVec.or_comm]
      exact ⟨Or.inr (Or.inl ⟨x, hx', by simp⟩), Or.inr (Or.inl ⟨x, hx', by simp⟩)⟩
    · obtain ⟨h1, h2⟩ := ih hx' hy'
      exact ⟨List.mem_append_right _ h1, List.mem_append_right _ h2⟩

def newChoices (ws : List T) : List T :=
  ((pairOps ws).filter (fun v => v != 0 && v != -1 && !ws.contains v)).eraseDups

lemma mem_newChoices {ws : List T} {z : T} (hz : possible ws z = true)
    (h0 : z ≠ 0) (h1 : z ≠ -1) (hm : z ∉ ws) : z ∈ newChoices ws := by
  unfold newChoices
  rw [List.mem_eraseDups, List.mem_filter]
  refine ⟨?_, ?_⟩
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
    rcases hz with (rfl | rfl) | ⟨u, hu, (rfl | rfl) | ⟨v, hv, rfl | rfl⟩⟩
    · exact (h0 rfl).elim
    · exact (h1 rfl).elim
    · exact (hm hu).elim
    · exact pairOps_not hu
    · by_cases huv : u = v
      · subst huv
        rw [BitVec.and_self] at hm
        exact (hm hu).elim
      · exact (pairOps_bin hu hv huv).1
    · by_cases huv : u = v
      · subst huv
        rw [BitVec.or_self] at hm
        exact (hm hu).elim
      · exact (pairOps_bin hu hv huv).2
  · simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', contains_false_iff]
    exact ⟨⟨h0, h1⟩, hm⟩

def masked (ws : List T) (mask want : T) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == mask || xs.any fun x =>
    x == want || (~~~x &&& mask) == want ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

def fastTwo (tgt : T) (ws : List T) : Bool :=
  !(masked ws (-1) tgt || masked ws (-1) (~~~tgt) ||
    ws.any fun x =>
      ((x &&& tgt) == tgt && masked ws x tgt) ||
      ((x ||| tgt) == tgt && masked ws (~~~x) (tgt &&& ~~~x)))

lemma masked_of_possible {ws : List T} {u : T} (hu : possible ws u = true) (m : T) :
    masked ws m (u &&& m) = true := by
  let xs := ws.map (fun x => x &&& m)
  have mem (x : T) (hx : x ∈ ws) : x &&& m ∈ xs := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp only [masked, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hu
  rcases hu with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst u
  · exact .inl (.inl (by simp))
  · exact .inl (.inr BitVec.allOnes_and)
  · exact .inr ⟨_, mem x hx, .inl (.inl (.inl rfl))⟩
  · refine .inr ⟨_, mem x hx, .inl (.inl (.inr ?_))⟩
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp
    cases x[i] <;> cases m[i] <;> rfl
  · refine .inr ⟨_, mem x hx, .inl (.inr ⟨?_, _, mem y hy, ?_⟩)⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide
  · refine .inr ⟨_, mem x hx, .inr ⟨?_, _, mem y hy, ?_⟩⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and, BitVec.getElem_or] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide

lemma fastTwo_safe {tgt : T} (ht0 : tgt ≠ 0) (ht1 : tgt ≠ -1) {ws : List T}
    (hf : fastTwo tgt ws = true) : safe tgt 2 ws := by
  simp only [fastTwo, Bool.not_eq_true', Bool.or_eq_false_iff, List.any_eq_false,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, not_or] at hf
  obtain ⟨⟨hn, hc⟩, hp⟩ := hf
  have hnot (u : T) (hu : possible ws u = true) :
      u ≠ tgt ∧ ~~~u ≠ tgt ∧ (∀ x ∈ ws, x &&& u ≠ tgt) ∧ (∀ x ∈ ws, x ||| u ≠ tgt) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro he
      have hh := masked_of_possible hu (-1)
      rw [bv_and_neg1, he, hn] at hh
      cases hh
    · intro he
      have hh := masked_of_possible hu (-1)
      have he' : u = ~~~tgt := by rw [← he, BitVec.not_not]
      rw [bv_and_neg1, he', hc] at hh
      cases hh
    · intro x hx he
      have hh := masked_of_possible hu x
      rw [BitVec.and_comm u x, he] at hh
      have hxt : x &&& tgt = tgt := by
        rw [← he, ← BitVec.and_assoc, BitVec.and_self]
      exact (hp x hx).1 ⟨hxt, hh⟩
    · intro x hx he
      have hh := masked_of_possible hu (~~~x)
      have he' : u &&& ~~~x = tgt &&& ~~~x := by
        rw [← he]
        apply BitVec.eq_of_getElem_eq
        intro i hi
        simp
        cases x[i] <;> cases u[i] <;> rfl
      rw [he'] at hh
      have hxt : x ||| tgt = tgt := by
        rw [← he, ← BitVec.or_assoc, BitVec.or_self]
      exact (hp x hx).2 ⟨hxt, hh⟩
  intro z hz v hv
  have H := hnot z hz
  have base (x : T) (hx : x ∈ ws) := hnot x (atom (.inr hx)).1
  have unary (x : T) (hx : x ∈ z :: ws) : x ≠ tgt ∧ ~~~x ≠ tgt := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨H.1, H.2.1⟩
    · exact ⟨(base x hx).1, (base x hx).2.1⟩
  have binary (x y : T) (hx : x ∈ z :: ws) (hy : y ∈ z :: ws) :
      x &&& y ≠ tgt ∧ x ||| y ≠ tgt := by
    rcases List.mem_cons.mp hx with hxe | hxm <;> rcases List.mem_cons.mp hy with hye | hym
    · simpa [hxe, hye] using H.1
    · simpa [hxe, BitVec.and_comm, BitVec.or_comm] using And.intro (H.2.2.1 y hym) (H.2.2.2 y hym)
    · simpa [hye] using And.intro (H.2.2.1 x hxm) (H.2.2.2 x hxm)
    · exact ⟨(base y hym).2.2.1 x hxm, (base y hym).2.2.2 x hxm⟩
  have hv' : v ≠ tgt := by
    simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hv
    rcases hv with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst v
    · exact ht0.symm
    · exact ht1.symm
    · exact (unary x hx).1
    · exact (unary x hx).2
    · exact (binary x y hx hy).1
    · exact (binary x y hx hy).2
  change (v :: z :: ws).contains tgt = false
  rw [contains_false_iff]
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · exact hv' he.symm
  · exact (unary tgt hm).1 rfl

def search (tgt : T) : ℕ → List T → Bool
  | 0, ws => fastTwo tgt ws
  | n + 1, ws => search tgt n ws && (newChoices ws).all (fun z => search tgt n (z :: ws))

lemma search_safe {tgt : T} (ht0 : tgt ≠ 0) (ht1 : tgt ≠ -1) {n : ℕ} {ws : List T}
    (h : search tgt n ws = true) : safe tgt (n + 2) ws := by
  induction n generalizing ws with
  | zero => exact fastTwo_safe ht0 ht1 h
  | succ n ih =>
    simp only [search, Bool.and_eq_true, List.all_eq_true] at h
    intro z hz
    by_cases h0 : z = 0
    · subst h0
      refine safe_mono ht0 ht1 ?_ (ih h.1)
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hx)
    · by_cases h1 : z = -1
      · subst h1
        refine safe_mono ht0 ht1 ?_ (ih h.1)
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hx)
      · by_cases hm : z ∈ ws
        · refine safe_mono ht0 ht1 ?_ (ih h.1)
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inr (Or.inr hm)
          · exact Or.inr (Or.inr hx)
        · exact ih (h.2 z (mem_newChoices hz h0 h1 hm))

lemma ins4_choices : newChoices ins4 = [
    0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333,
    0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0x0f0f, 0xf000, 0xfff0, 0x00ff] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
lemma safe4_fce8 : safe 0xfce8 4 ins4 := by
  apply search_safe (by decide) (by decide) (n := 2)
  rw [search, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  rw [ins4_choices]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
lemma safe4_feea : safe 0xfeea 4 ins4 := by
  apply search_safe (by decide) (by decide) (n := 2)
  rw [search, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  rw [ins4_choices]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

def assign4 (k : Fin 16) (i : Fin 4) : Bool := bit k (ins4.getD i.val 0)

def fn_fce8 (y : Fin 4 → Bool) : Bool :=
  (y 0 && y 1) || (y 0 && y 2) || (y 1 && y 2) || (y 1 && y 3) || (y 2 && y 3)

def fn_feea (y : Fin 4 → Bool) : Bool :=
  y 0 || (y 1 && y 2) || (y 1 && y 3) || (y 2 && y 3)

lemma no_size4_fce8 : ¬ HasCircuitSize 4 fn_fce8 4 := by
  rintro ⟨C, hg, hsize, he⟩
  apply exclude 0xfce8 (by decide) C.gates C.output hg ins4 ins4 (fun _ h => h) 4 hsize safe4_fce8
  intro k
  have hi : ∀ t : Fin 16, List.ofFn (assign4 t) = ins4.map (bit t) := by decide
  have ht : ∀ t : Fin 16, fn_fce8 (assign4 t) = bit t 0xfce8 := by decide
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using he (assign4 k)

lemma no_size4_feea : ¬ HasCircuitSize 4 fn_feea 4 := by
  rintro ⟨C, hg, hsize, he⟩
  apply exclude 0xfeea (by decide) C.gates C.output hg ins4 ins4 (fun _ h => h) 4 hsize safe4_feea
  intro k
  have hi : ∀ t : Fin 16, List.ofFn (assign4 t) = ins4.map (bit t) := by decide
  have ht : ∀ t : Fin 16, fn_feea (assign4 t) = bit t 0xfeea := by decide
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using he (assign4 k)

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have h1 : wiresFrom (g :: gs) w = wiresFrom gs (step w g) := rfl
    rw [h1, ht]
    simp [step]

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]
  simp [hl]

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h
  simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := legal g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

lemma normGate_nok (g : Gate) (h : legal g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  change op = .and ∨ op = .or ∨ op = .not at hop
  rcases hop with rfl | rfl | rfl
  · exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate]

lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate) (step w (normGate g)) := rfl
    have s2 : wiresFrom (g :: gs) w = wiresFrom gs (step w g) := rfl
    have hs : step w (normGate g) = step w g := by
      simp only [step, normGate_eval]
    rw [s1, s2, hs, ih]

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, legal g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; simp [legal]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; simp [legal]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; subst hg; simp [legal]
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, Stat.Valid w.length s) :
    Stat.Valid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    Stat.val (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k <;> (try cases c) <;> (try cases d) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom, step]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k <;> (try cases c) <;> (try cases d) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom, step]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom, step]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

lemma elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    have h : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, legal g) → ∀ g ∈ (elim n gs acc).2, legal g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    omega

lemma elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]
        simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]
          exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

lemma elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]
  simp

lemma elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

lemma stat_valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, Stat.Valid m s → Stat.Valid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma stat_val_append (w t : List Bool) : ∀ s : Stat, Stat.Valid w.length s →
    Stat.val (w ++ t) s = Stat.val w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    Stat.Valid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    Stat.val (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, legal g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (step w g) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']
        exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      simp [wiresFrom, w', List.foldl_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, step, hl], ?_⟩
    intro i
    show Stat.Valid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      Stat.val (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, step, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, step, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨stat_valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, stat_val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr i.val) ++ [Sum.inl b]

lemma inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

lemma ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

lemma split_first_read (k : ℕ) (gs : List Gate) (h : ∃ g ∈ gs, k ∈ g.inputs) :
    ∃ pre g post, gs = pre ++ g :: post ∧ (∀ g' ∈ pre, k ∉ g'.inputs) ∧ k ∈ g.inputs := by
  induction gs with
  | nil => obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons a rest ih =>
    by_cases ha : k ∈ a.inputs
    · exact ⟨[], a, rest, rfl, by simp, ha⟩
    · have hr : ∃ g ∈ rest, k ∈ g.inputs := by
        obtain ⟨g, hg, hkg⟩ := h
        rcases List.mem_cons.mp hg with rfl | hg
        · exact (ha hkg).elim
        · exact ⟨g, hg, hkg⟩
      obtain ⟨pre, g, post, rfl, hpre, hg⟩ := ih hr
      refine ⟨a :: pre, g, post, rfl, ?_, hg⟩
      intro g' hg'
      rcases List.mem_cons.mp hg' with rfl | hg'
      · exact ha
      · exact hpre g' hg'

lemma wires_agree_avoid (bad : ℕ → Prop) (gs : List Gate)
    (hgs : ∀ g ∈ gs, ∀ i ∈ g.inputs, ¬ bad i) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i, ¬ bad i → w1.getD i false = w2.getD i false) →
      ∀ i, ¬ bad i → (wiresFrom gs w1).getD i false = (wiresFrom gs w2).getD i false := by
  induction gs with
  | nil => intro w1 w2 _ h i hi; exact h i hi
  | cons g gs ih =>
    intro w1 w2 hlen h
    have hg := hgs g List.mem_cons_self
    have hev : g.op.eval (g.inputs.map fun i => w1.getD i false) =
        g.op.eval (g.inputs.map fun i => w2.getD i false) := by
      congr 1
      exact List.map_congr_left fun i hi => h i (hg i hi)
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (step w1 g) (step w2 g)
      (by simp [step, hlen])
    intro i hi
    simp only [step, hev]
    by_cases hlt : i < w1.length
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
      exact h i hi
    · by_cases heq : i = w1.length
      · rw [heq, getD_snoc_eq, hlen, getD_snoc_eq]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def t5bb (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3)

lemma t5bb_snoc_false (y : Fin 4 → Bool) : t5bb (Fin.snoc y false) = fn_fce8 y := by
  simp [t5bb, fn_fce8, Fin.snoc]
  rfl

lemma t5bb_snoc_true (y : Fin 4 → Bool) : t5bb (Fin.snoc y true) = fn_feea y := by
  cases h0 : y 0
  · simp [t5bb, fn_feea, Fin.snoc, h0]
    rfl
  · simp [t5bb, fn_feea, Fin.snoc, h0]

lemma t5bb_dep4 : t5bb (Fin.snoc (![true, false, false, false]) false) ≠
    t5bb (Fin.snoc (![true, false, false, false]) true) := by
  decide

lemma t5bb_nc (b : Bool) : ∃ y1 y2 : Fin 4 → Bool,
    t5bb (Fin.snoc y1 b) ≠ t5bb (Fin.snoc y2 b) := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  cases b <;> decide

lemma main (t : ℕ) (h : HasCircuitSize 5 t5bb t) : 7 ≤ t := by
  by_contra! hlt
  have ht6 : t ≤ 6 := by omega
  obtain ⟨C, hok, hsz, hev⟩ := h
  have hlen : C.gates.length ≤ 6 := hsz.trans ht6
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g0 (hok g0 hg0)
  have hglen : gs.length ≤ 6 := by simp [hgs, hlen]
  have hevg : ∀ x : Fin 5 → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = t5bb x := by
    intro x
    rw [hgs, wiresFrom_norm]
    exact hev x
  have hread4 : ∃ g ∈ gs, 4 ∈ g.inputs := by
    by_contra hno
    push Not at hno
    by_cases hout4 : C.output = 4
    · have h0 := hevg (Fin.snoc (![false, false, false, false]) true)
      rw [hout4] at h0
      obtain ⟨tl, htl, _⟩ := wiresFrom_start gs (List.ofFn (Fin.snoc (![false, false, false, false]) true))
      rw [htl, List.getD_append _ _ _ _ (by simp)] at h0
      have hval : (List.ofFn (Fin.snoc (![false, false, false, false]) true)).getD 4 false = true := by decide
      rw [hval] at h0
      have hf : t5bb (Fin.snoc (![false, false, false, false]) true) = false := by decide
      rw [hf] at h0
      cases h0
    · apply t5bb_dep4
      rw [← hevg, ← hevg]
      apply wires_agree_avoid (fun i => i = 4) gs
        (fun g hg i hi heq => hno g hg (heq ▸ hi))
        _ _ (by simp) _ C.output hout4
      intro i hi
      by_cases h5 : i < 5
      · have h4 : i < 4 := by omega
        rw [ofFn_snoc, ofFn_snoc, List.getD_append _ _ _ _ (by simp; omega),
          List.getD_append _ _ _ _ (by simp; omega)]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  obtain ⟨pre, g, post, hsplit, hpre_no4, hg4⟩ := split_first_read 4 gs hread4
  have hgnok : NOk g := hnok g (by rw [hsplit]; simp)
  have hpost_nok : ∀ g' ∈ post, NOk g' := fun g' hg' => hnok g' (by rw [hsplit]; simp [hg'])
  let b : Bool := fixBit g
  set acc1 := elim 4 pre (initStats 4 b, []) with hacc1
  set acc2 := elimStep 4 acc1 g with hacc2
  set acc := elim 4 post acc2 with hacc
  have hacc_eq : acc = elim 4 gs (initStats 4 b, []) := by
    rw [hsplit, elim_append]
    rfl
  have hacc1_len : acc1.1.length = 5 + pre.length := by
    rw [hacc1, elim_fst_len]
    simp [initStats]
  have hacc1_4 : acc1.1.getD 4 (Sum.inl false) = Sum.inl b := by
    rw [hacc1, elim_getD 4 4 _ pre _ (by simp [initStats])]
    exact getD_snoc_len _ _ _ _ (by simp)
  have hacc2_len : acc2.2.length = acc1.2.length :=
    elimStep_none 4 acc1 g hgnok 4 hg4 b hacc1_4
  have hacc2_4 : acc2.1.getD 4 (Sum.inl false) = Sum.inl b := by
    rw [hacc2]
    simp only [elimStep]
    rw [getD_snoc_ne _ _ _ _ (by omega)]
    exact hacc1_4
  obtain ⟨c, hacc2_g⟩ := elimStep_const 4 acc1 g hgnok 4 hg4 hacc1_4
  rw [hacc1_len] at hacc2_g
  have hacc2_1len : acc2.1.length = 5 + pre.length + 1 := by
    rw [hacc2]
    simp only [elimStep, List.length_append, List.length_singleton, hacc1_len]
  have hpre_bound : acc1.2.length ≤ pre.length := by
    have := elim_len 4 pre (initStats 4 b, [])
    simpa [hacc1] using this
  have hlen_sum : pre.length + 1 + post.length = gs.length := by
    rw [hsplit]
    simp only [List.length_append, List.length_cons]
    omega
  have hinv : ∀ y : Fin 4 → Bool,
      Inv 4 (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b))) acc := by
    intro y
    rw [hacc_eq, ofFn_snoc]
    exact inv_elim 4 _ (by simp) gs _ _ (fun g' hg' => (hnok g' hg').1) (inv_init 4 b y)
  have hval : ∀ y : Fin 4 → Bool,
      Stat.val (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false)) =
        t5bb (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hout_wire : ∃ j : ℕ, acc.1.getD C.output (Sum.inl false) = Sum.inr j := by
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c0 =>
      exfalso
      obtain ⟨y1, y2, hne⟩ := t5bb_nc b
      apply hne
      rw [← hval y1, ← hval y2, hst]
      rfl
    | inr j => exact ⟨j, rfl⟩
  obtain ⟨j, hj⟩ := hout_wire
  have hdrop2 : acc.2.length ≤ 4 := by
    by_cases hrg : ∃ h' ∈ post, 5 + pre.length ∈ h'.inputs
    · have h1 := elim_len_lt 4 (5 + pre.length) post acc2 hpost_nok (by omega) ⟨c, hacc2_g⟩ hrg
      rw [← hacc, hacc2_len] at h1
      omega
    · by_cases hr4 : ∃ h' ∈ post, 4 ∈ h'.inputs
      · have h1 := elim_len_lt 4 4 post acc2 hpost_nok (by omega) ⟨b, hacc2_4⟩ hr4
        rw [← hacc, hacc2_len] at h1
        omega
      · exfalso
        push Not at hrg hr4
        have hout4 : C.output ≠ 4 := by
          intro e
          rw [e, hacc, elim_getD 4 4 _ post acc2 (by omega), hacc2_4] at hj
          cases hj
        have houtg : C.output ≠ 5 + pre.length := by
          intro e
          rw [e, hacc, elim_getD 4 (5 + pre.length) _ post acc2 (by omega), hacc2_g] at hj
          cases hj
        apply t5bb_dep4
        rw [← hevg, ← hevg, hsplit]
        set w0 := List.ofFn (Fin.snoc (![true, false, false, false]) false)
        set w1 := List.ofFn (Fin.snoc (![true, false, false, false]) true)
        have hp_eq : ∀ i, i ≠ 4 → (wiresFrom pre w0).getD i false = (wiresFrom pre w1).getD i false := by
          apply wires_agree_avoid (fun i => i = 4) pre
            (fun g' hg' i hi heq => hpre_no4 g' hg' (heq ▸ hi)) w0 w1 (by simp [w0, w1])
          intro i hi
          by_cases h5 : i < 5
          · dsimp only [w0, w1]
            rw [ofFn_snoc, ofFn_snoc, List.getD_append _ _ _ _ (by simp; omega),
              List.getD_append _ _ _ _ (by simp; omega)]
          · rw [List.getD_eq_default _ _ (by simp [w0]; omega),
              List.getD_eq_default _ _ (by simp [w1]; omega)]
        have hlen_p0 : (wiresFrom pre w0).length = 5 + pre.length := by
          rw [length_wiresFrom]; simp [w0]
        have hlen_p1 : (wiresFrom pre w1).length = 5 + pre.length := by
          rw [length_wiresFrom]; simp [w1]
        have hstep_eq : ∀ i, ¬ (i = 4 ∨ i = 5 + pre.length) →
            (step (wiresFrom pre w0) g).getD i false = (step (wiresFrom pre w1) g).getD i false := by
          intro i hi
          have hne4 : i ≠ 4 := fun h => hi (Or.inl h)
          have hneg : i ≠ 5 + pre.length := fun h => hi (Or.inr h)
          simp only [step]
          rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
          exact hp_eq i hne4
        have hfold_eq : ∀ w, wiresFrom (pre ++ g :: post) w =
            wiresFrom post (step (wiresFrom pre w) g) := by
          intro w
          simp [wiresFrom, List.foldl_append]
        rw [hfold_eq w0, hfold_eq w1]
        exact wires_agree_avoid (fun i => i = 4 ∨ i = 5 + pre.length) post
          (fun g' hg' i hi hbad => hbad.elim (fun h => hr4 g' hg' (h ▸ hi)) (fun h => hrg g' hg' (h ▸ hi)))
          (step (wiresFrom pre w0) g) (step (wiresFrom pre w1) g)
          (by simp [step, hlen_p0, hlen_p1]) hstep_eq C.output (not_or.mpr ⟨hout4, houtg⟩)
  have hhas4 : HasCircuitSize 4 (fun y => t5bb (Fin.snoc y b)) 4 := by
    refine ⟨⟨acc.2, j⟩, ?_, hdrop2, ?_⟩
    · rw [hacc_eq]
      exact elim_ok 4 gs (initStats 4 b, []) (by simp)
    · intro y
      have hy := hval y
      rw [hj] at hy
      exact hy
  cases hb : b
  · rw [hb] at hhas4
    have hfun : (fun y => t5bb (Fin.snoc y false)) = fn_fce8 := funext t5bb_snoc_false
    rw [hfun] at hhas4
    exact no_size4_fce8 hhas4
  · rw [hb] at hhas4
    have hfun : (fun y => t5bb (Fin.snoc y true)) = fn_feea := funext t5bb_snoc_true
    rw [hfun] at hhas4
    exact no_size4_feea hhas4

end PEqualNP.Outside.L_meta_5451

theorem PEqualNP.Outside.L_meta_5451 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3)) t → 7 ≤ t :=
  PEqualNP.Outside.L_meta_5451.main
