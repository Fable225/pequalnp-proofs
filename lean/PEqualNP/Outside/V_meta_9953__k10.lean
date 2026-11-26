import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.V_meta_9953__k10

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
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
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
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
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
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

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
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

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩




open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

inductive Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs → Run inv meet join y s xs → Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def shift (K a : ℕ) : ℕ := if a < K then a else a - 1

def shGate (K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift K)⟩

def RelD (K : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ K ≤ W'.length ∧
    ∀ a, a ≠ K → W'.getD (shift K a) false = W.getD a false

theorem relD_wires (K : ℕ) (post : List Gate) : ∀ W W' : List Bool,
    (∀ g ∈ post, K ∉ g.inputs) → RelD K W W' →
    RelD K (wiresFrom post W) (wiresFrom (post.map (shGate K)) W') := by
  induction post with
  | nil => intro W W' _ h; exact h
  | cons g post ih =>
    intro W W' hno h
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [shGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun e => hno g List.mem_cons_self (e ▸ ha))
    have s1 : wiresFrom (g :: post) W
        = wiresFrom post (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom ((g :: post).map (shGate K)) W'
        = wiresFrom (post.map (shGate K))
          (W' ++ [(shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)]) := rfl
    rw [s1, s2, hv]
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro a haK
    rcases Nat.lt_trichotomy a W.length with hw | hw | hw
    · have hlt : shift K a < W'.length := by
        unfold shift; split <;> omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 a haK
    · have he : shift K a = W'.length := by
        unfold shift; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ shift K a := by
        unfold shift; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem del_gate (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (f : BFn n)
    (hok : ∀ g' ∈ pre ++ g :: post, Ok g')
    (hno : ∀ g' ∈ post, n + pre.length ∉ g'.inputs) (ho : o ≠ n + pre.length)
    (hev : ∀ x, val (pre ++ g :: post) n o x = f x) :
    HasCircuitSize n f (pre.length + post.length) := by
  refine ⟨⟨pre ++ post.map (shGate (n + pre.length)), shift (n + pre.length) o⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hok g' (List.mem_append_left _ h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hok g0 (List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨this.1, by simpa [shGate] using this.2⟩
  · simp [Circuit.size]
  · intro x
    rw [← hev x]
    show (wiresFrom (pre ++ post.map (shGate (n + pre.length))) (List.ofFn x)).getD
      (shift (n + pre.length) o) false = _
    unfold val
    have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
        (wiresFrom pre (List.ofFn x) ++
          [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [wiresFrom_append]; rfl
    have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]; simp
    rw [h1, wiresFrom_append]
    refine (relD_wires (n + pre.length) post _ _ hno ⟨by simp, by omega, ?_⟩).2.2 o ho
    intro a ha
    by_cases hlt : a < n + pre.length
    · have : shift (n + pre.length) a = a := by simp [shift, hlt]
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have : shift (n + pre.length) a = a - 1 := by simp [shift, hlt]
      rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    
    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
        Run (invF (n := n)) meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hj h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
          simp only [decide_eq_true_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hj, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · apply single j true
      · intro a; simp [hinp]
      · funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval]
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
      · have hjm := hin j (by simp [hinp])
        have hkm := hin k (by simp [hinp])
        have hke : k ∈ (liveList gs n o p).erase j :=
          (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
        have hp1 : (liveList gs n o p).Perm
            (j :: k :: ((liveList gs n o p).erase j).erase k) :=
          (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
        have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
            a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
          intro a
          rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
              (kept (decide (Live gs o (p + 1) k)) k
                (((liveList gs n o p).erase j).erase k))) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
            · rw [mem_kept, mem_kept]
              rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
              · exact hnew j hjm h.symm
              · exact hnew k hkm h.symm
              · exact hnew _ ((hmr _).1 h).2.2 rfl
            · rw [hmr]; simp
            · rw [mem_kept, hmr]
              rintro (⟨_, h⟩ | h)
              · exact hjk h
              · exact h.2.1 rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
            simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                · by_cases hak : a = k
                  · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hjm, fun _ => h1⟩
              · exact Or.inr ⟨hkm, fun _ => h1⟩
              · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
            then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
          funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length = t ∧
    ∀ x, val gs n o x = f x
  have hP : ∀ t, HasCircuitSize n f t → ∃ t', t' ≤ t ∧ P t' := by
    intro t ht
    obtain ⟨gs, o, hcl, hsz, hev⟩ := clean_of n f t hnc ht
    exact ⟨gs.length, hsz, gs, o, hcl, rfl, hev⟩
  obtain ⟨t0, ht0, hPt0⟩ := hP s h
  have hex : ∃ t, P t := ⟨t0, hPt0⟩
  have hmin : Nat.find hex ≤ t0 := Nat.find_min' hex hPt0
  obtain ⟨gs, o, hcl, hlen, hev⟩ := Nat.find_spec hex
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have ho : o < n + gs.length := by
    by_contra hge
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hev y, ← hev y']
    unfold val
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
      List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra hcon
    push Not at hcon
    obtain ⟨hpo, hno⟩ := hcon
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
    have hsz := del_gate n pre g post o f hok (by
      intro g' hg'
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
      have := hno (pre.length + 1 + q) g' (by
        rw [List.getElem?_append_right (by omega)]
        have e : pre.length + 1 + q - pre.length = q + 1 := by omega
        rw [e]; simpa using hq)
      rw [hpl]; exact this) (by rw [hpl]; exact fun e => hpo e.symm) hev
    obtain ⟨t', ht', hPt'⟩ := hP _ hsz
    have := Nat.find_min' hex hPt'
    simp at hlen
    omega
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)





theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf




open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

def rows9953 : List ℕ := [6, 6, 6, 6, 6, 6, 6, 6, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 1, 1, 2, 2, 4, 4, 4, 6, 6, 6, 6, 16, 17, 17, 18, 18, 18, 10, 10, 10, 10, 10, 10, 10, 10, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 1, 1, 2, 2, 8, 8, 8, 10, 10, 10, 10, 16, 17, 17, 18, 18, 18, 36, 36, 36, 36, 36, 36, 36, 36, 17, 17, 17, 17, 17, 48, 48, 48, 48, 48, 48, 1, 1, 32, 32, 4, 4, 4, 36, 36, 36, 36, 16, 17, 17, 48, 48, 48, 40, 40, 40, 40, 40, 40, 40, 40, 17, 17, 17, 17, 17, 48, 48, 48, 48, 48, 48, 1, 1, 32, 32, 8, 8, 8, 40, 40, 40, 40, 16, 17, 17, 48, 48, 48, 3, 5, 9, 12, 20, 24, 33, 34, 3, 5, 12, 20, 34, 3, 5, 12, 20, 33, 34, 3, 5, 3, 34, 5, 12, 20, 7, 14, 22, 38, 20, 19, 21, 19, 22, 50, 3, 9, 5, 12, 24, 20, 33, 34, 3, 9, 12, 24, 34, 3, 9, 12, 24, 33, 34, 3, 9, 3, 34, 9, 12, 24, 11, 14, 26, 42, 24, 19, 25, 19, 26, 50, 33, 5, 9, 12, 20, 24, 3, 34, 33, 5, 12, 20, 34, 33, 5, 12, 20, 3, 34, 33, 5, 33, 34, 5, 12, 20, 37, 44, 52, 38, 20, 49, 21, 49, 52, 50, 33, 9, 5, 12, 24, 20, 3, 34, 33, 9, 12, 24, 34, 33, 9, 12, 24, 3, 34, 33, 9, 33, 34, 9, 12, 24, 41, 44, 56, 42, 24, 49, 25, 49, 56, 50]

def xs9953 : List ℕ := [0x384ba6347384ba6347384ba6347384ba6347180181f00180181f00180181f00180181f00, 0x8204610c08204610c0ebc6c3181ebc6c3181000000000000000000e3c67e0ffe3c67e0ff, 0x900842c57f91ce1a00900842c57f91ce1a00000000003f8000ff00000000003f8000ff, 0x57f91ce1a00900842c57f91ce1a00900842c03f8000ff00000000003f8000ff000000000, 0xfd2010830fd2010830fd2010830fd2010830fc007ff00fc007ff00fc007ff00fc007ff00, 0xebc6c3181ebc6c31818204610c08204610c0e3c67e0ffe3c67e0ff000000000000000000]

abbrev f9953 : BFn 6 := fun x : Fin 6 → Bool =>
  (18446461426206309032 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)

def f9953Fast (x : Fin 6 → Bool) : Bool :=
  (18446461426206309032 : ℕ).testBit
    ((if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
     (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0))

theorem f9953_eq : f9953 = f9953Fast := by
  funext x; revert x; decide +kernel

theorem rows9953_len : rows9953.length = 288 := by decide +kernel

theorem enc_inputs9953 :
    (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map (fun a => encL a rows9953)
      = xs9953 := by decide +kernel

theorem enc_goal9953_fast : encL f9953Fast rows9953 = goal 144 := by decide +kernel

theorem enc_goal9953 : encL f9953 rows9953 = goal 144 := by
  rw [f9953_eq]; exact enc_goal9953_fast

theorem mask9953 : mask 144 = 2 ^ rows9953.length - 1 := by decide +kernel

theorem proper_fail9953 : ∀ zs ∈ xs9953.sublists, zs ≠ xs9953 →
    (cov 144 zs &&& lo 144) ≠ lo 144 := by decide +kernel

theorem no_sub9953 (noRunFull : ∀ s ≤ 9, ¬ NatRun (mask 144) (goal 144) s xs9953) :
    ∀ s ≤ 9, ∀ zs : List ℕ, zs.Sublist xs9953 → NatRun (mask 144) (goal 144) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xs9953
  · subst e; exact noRunFull s hs h
  · exact proper_fail9953 zs (List.mem_sublists.2 hz) e (required h)

theorem main9953 (noRunFull : ∀ s ≤ 9, ¬ NatRun (mask 144) (goal 144) s xs9953) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 6 f9953 9 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run f9953 ⟨fun _ => false, fun _ => true, by decide⟩ 9 h
  have hr : NatRun (mask 144) (encL f9953 rows9953) s' (ws.map fun a => encL a rows9953) :=
    Run.map (fun a : BFn 6 => encL a rows9953)
      (fun a => by rw [mask9953]; exact encL_inv a rows9953)
      (fun a b => encL_and a b rows9953) (fun a b => encL_or a b rows9953) hrun
  rw [enc_goal9953] at hr
  refine no_sub9953 noRunFull s' (by omega) _ ?_ hr
  rw [← enc_inputs9953]
  exact hsub.map _

def blockWord (d : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | q::r, w => ((w >>> (d*q)) &&& lo d) ||| (blockWord d r w <<< d)

theorem block_hom (d : Nat) (qs : List Nat) (a b : Nat) :
    blockWord d qs (a &&& b) = (blockWord d qs a &&& blockWord d qs b) ∧
    blockWord d qs (a ||| b) = (blockWord d qs a ||| blockWord d qs b) ∧
    blockWord d qs (a ^^^ b) = (blockWord d qs a ^^^ blockWord d qs b) := by
  induction qs with
  | nil => simp [blockWord]
  | cons q qs ih =>
    refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
      by_cases hj : d ≤ j <;>
      simp [blockWord,lo,Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hj, ih,
        Nat.not_lt_of_ge, Nat.lt_of_not_ge] <;> grind

theorem block_run {s ws k} (h : NatRun (mask k) (goal k) s ws)
    (d : Nat) (qs : List Nat) (hm : blockWord d qs (mask k) = mask k)
    (hg : blockWord d qs (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (blockWord d qs)) := by
  rw [← hg]
  exact Run.map _ (fun a => (block_hom d qs a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (block_hom d qs a b).1) (fun a b => (block_hom d qs a b).2.1) h





theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]





def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]





def unpackWords (wt : Nat → Nat) (bits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | t+1, v => if v = 0 then [] else
      wt (v &&& (2^bits-1)) :: unpackWords wt bits t (v >>> bits)

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih





def edgeHash : List Nat → Nat
  | [] => 0
  | w :: t => (w % 4294967291 + 317)^3 % 4294967291 + 1 + edgeHash t

def barrier (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (act : Nat → Nat → Nat → Nat) (wits : Nat → Nat)
    (rot : Nat → List Nat → List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (mask k) (s+2-ws.length) ws fun tag zs =>
        covers k s zs && (
          let v := act (s+1) i tag
          if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
          else !(v/16 < N s && (rot (v/2 % 8) zs).isPerm (S s (v/16)))))

theorem barrier_sound {k S N act wits rot} {s i} (hb : barrier k S N act wits rot s i = true)
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [barrier,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) := covers k s zs && (
      let v := act (s+1) i tag
      if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
      else !(v/16 < N s && (rot (v/2 % 8) zs).isPerm (S s (v/16))))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F,covers_ok hz,Bool.true_and]
      split
      · simp [scoreCheck_no hz]
      · simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (hr _ hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barrier_all {k S N act wits rot} {cap : Nat}
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barrier k S N act wits rot s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := barrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h


def t1 : Nat := 0x0
def t2 : Nat := 0x4000000000000000000000000000000000000000000
def t3 : Nat := 0x410000000000000000000000000000000000000000000
def t4 : Nat := 0x8000000008000000000000000000000000000000000000000000
def t5 : Nat := 0x280000000280000000000000000000000000000000000000000000
def t6 : Nat := 0x20000000000000000020000000000000000000000000000000000000000000
def t7 : Nat := 0x2000000000800000043c00000000000000000000000000000000003c0000ff
def t8 : Nat := 0x100000000000000000100000000000000000000000000000000000000000000
def t9 : Nat := 0x4104904202000000004104904202000000000000000000000000000000000000
def t10 : Nat := 0x412490420200800000453c90420200000000000000000000000000003c0000ff
def t11 : Nat := 0x20552010810000000020552010810000000000000000000000000000000000000
def t12 : Nat := 0x2057201081000800002057e01081000000000000000000000000000003c0000ff
def t13 : Nat := 0x24556914a12000000024556914a12000000000000000000000000000000000000
def t14 : Nat := 0x24576914a12000000024576914a1200000000003f8000ff00000000003f8000ff
def t15 : Nat := 0x20040000020040284282101284282101000000000000000000000000000000000000
def t16 : Nat := 0x2004000002004069c28210169c282101000000000000000000e3c67e0ffe3c67e0ff
def t17 : Nat := 0x2004002002004028c2821016bc28210100000000000000000000000000003c0000ff
def t18 : Nat := 0x20044104924242284282105384b86303000000000000000000000000000000000000
def t19 : Nat := 0x20064142934a522802821257d6b96b131c0181f001c3981f00fc07fff00fffffffff
def t20 : Nat := 0x6e31c5024fe73c30006e31c5024fe73c300078000003ff800ff00078000003ff800ff
def t21 : Nat := 0x100842c14391ce1a00900842c55f91ce1a00000000000380000000000000003f8000ff
def t22 : Nat := 0x192c64e00192c64e00db8e70f00db8e70f00398000000398000003ff800ff03ff800ff
def t23 : Nat := 0x192c66e14393ce5e28db8e72f7dfb9ef1f1c3981f001c3981f00ffffffffffffffffff
def t24 : Nat := 0x4ba6347004ba6347004ba6347004ba6347000180000000180000000180000000180000
def t25 : Nat := 0x800000043c00000000800000043c00000000000000003c0000ff00000000003c0000ff
def t26 : Nat := 0x9008408009008408009008408009008408000000000000000000000000000000000000
def t27 : Nat := 0x900840802900840800900840843d00840800000000000000000000000000003c0000ff
def t28 : Nat := 0x900840c02d90c60a00900840c02d90c60a00000000003f8000ff00000000003f8000ff
def t29 : Nat := 0x900840c10d90c60a00900840c10d90c60a000000000000000000000000000000000000
def t30 : Nat := 0x900842847b018c1800900842847b018c1800000000003f8000ff00000000003f8000ff
def t31 : Nat := 0x900842855b018c1800900842855b018c18000000000000000000000000000000000000
def t32 : Nat := 0x900842c55f91ce1a00900842c55f91ce1a000000000000000000000000000000000000
def t33 : Nat := 0x900842c55f91ce1a00900842c55f91ce1a00000000003f8000ff00000000003f8000ff
def t34 : Nat := 0x900842c57b91ce1a00900842c57f91ce1a00000000003f8000ff00000000003f8000ff
def t35 : Nat := 0x900842c57f91ce1a00900842c57f91ce1a00000000003f8000ff00000000003f8000ff
def t36 : Nat := 0x902846c57f93ce5a28d28a52d7ffb9ef1b00000000003f8000ff00000000003f8000ff
def t37 : Nat := 0xdbae74f00dbae74f00dbae74f00dbae74f03ff800ff03ff800ff03ff800ff03ff800ff
def t38 : Nat := 0x2000000002000000043c00000043c00000000000000000000000003c0000ff03c0000ff
def t39 : Nat := 0x204610c00204610c002c6c318102c6c318100000000000000000003c6000ff03c6000ff
def t40 : Nat := 0x24fe73c7024fe73c7024fe73c7024fe73c703ff800ff03ff800ff03ff800ff03ff800ff
def t41 : Nat := 0x2900842c57f91ce1a43d00842c57f91ce1a00000000003f8000ff03c0000ff03f8000ff
def t42 : Nat := 0x2944948802944948802944948802944948803fe000ff03fe000ff03fe000ff03fe000ff
def t43 : Nat := 0x296eb5cd02dfef7cb0296eb5cd02dfef7cb03ff800ff03ff800ff03ff800ff03ff800ff
def t44 : Nat := 0x29d6d6ce029d6d6ce02dfcf78f02dfcf78f03ff800ff03ff800ff03ff800ff03ff800ff
def t45 : Nat := 0x2d90c60e02d90c60e02d90c60e02d90c60e03f8000ff03f8000ff03f8000ff03f8000ff
def t46 : Nat := 0x2dfef7cf02dfef7cf02dfef7cf02dfef7cf03ff800ff03ff800ff03ff800ff03ff800ff
def t47 : Nat := 0x2dfef7cf02dfef7cf2adfef7cf2adfef7cf03ff800ff03ff800ff03ff800ff03ff800ff
def t48 : Nat := 0x2dfef7cf12dfef7cf02dfef7cf12dfef7cf03ff800ff03ff800ff03ff800ff03ff800ff
def t49 : Nat := 0x2dfef7ef57fffffdf02dfef7ef57fffffdf03ff800ff03ff800ff03ff800ff03ff800ff
def t50 : Nat := 0x43018c38043018c3845b018c3845b018c38043800000043800000e7fe7e0ffe7fe7e0ff
def t51 : Nat := 0x43038c7c14393ce7a6db29ad3d7dfb9ef3b1c3981f001c3981f00ffffffffffffffffff
def t52 : Nat := 0x100924246100924246384b86307384b86307180181f00180181f00180181f00180181f00
def t53 : Nat := 0x10092424610092424679cb8630779cb86307180181f00180181f00fbc7ffffffbc7fffff
def t54 : Nat := 0x104904206104904206104904206104904206000000000000000000000000000000000000
def t55 : Nat := 0x10d90c62e57f91ce1e10d90c62e57f91ce1e00000000003f8000ff00000000003f8000ff
def t56 : Nat := 0x1420108301420108307d20108307d20108301c0001f001c0001f00fc007ff00fc007ff00
def t57 : Nat := 0x142934a76142934a767d6b96b377d6b96b371c3981f001c3981f00ffffffffffffffffff
def t58 : Nat := 0x14391ce3e14391ce3e14391ce3e14391ce3e1c3981f001c3981f001c3981f001c3981f00
def t59 : Nat := 0x14391ce3e14391ce3e55b91ce3e55b91ce3e1c3981f001c3981f00ffffffffffffffffff
def t60 : Nat := 0x14393ce7e14393ce7e7dfb9ef3f7dfb9ef3f1c3981f001c3981f00ffffffffffffffffff
def t61 : Nat := 0x14393ce7e14793ce7e7dfb9ef3f7dfb9ef3f1c3981f001c3981f00ffffffffffffffffff
def t62 : Nat := 0x14393ce7e55393ce7e7dfb9ef3f7dfb9ef3f1c3981f001c3981f00ffffffffffffffffff
def t63 : Nat := 0x14b93ce7e14b93ce7e7dfb9ef3f7dfb9ef3f1c3981f001c3981f00ffffffffffffffffff
def t64 : Nat := 0x14b93ce7e57f93ce7e7dfb9ef3f7ffb9ef3f1c3981f001ff981fffffffffffffffffffff
def t65 : Nat := 0x16fffffff16fffffff7ffffffff7ffffffff1fff81fff1fff81fffffffffffffffffffff
def t66 : Nat := 0x2802a2145384ba63432802a2145384ba6343180181f00180181f00180181f00180181f00
def t67 : Nat := 0x2802a21657d6bb6b532802a21657d6bb6b53fc07fff00ffffffffffc07fff00fffffffff
def t68 : Nat := 0x2842a21412842a21412842a21412842a2141000000000000000000000000000000000000
def t69 : Nat := 0x284ba6347384ba6347284ba6347384ba6347180181f00180181f00180181f00180181f00
def t70 : Nat := 0x380000000380000000380000000380000000180001f00180001f00180001f00180001f00
def t71 : Nat := 0x380000004384904202380000004384904202180001f00180001f00180001f00180001f00
def t72 : Nat := 0x3800000207d20108103800000207d2010810180001f00180001f00180001f00180001f00
def t73 : Nat := 0x380020040380020040384282101384282101180001f00180001f00180001f00180001f00
def t74 : Nat := 0x384ba6347384ba6347384ba6347384ba6347180181f00180181f00180181f00180181f00
def t75 : Nat := 0x384ba6347384ba6347384ba6347794ba6347180181f00180181f00180181f00180181f00
def t76 : Nat := 0x384ba6347384ba634738cba634738cba6347180181f00180181f00180181f00180181f00
def t77 : Nat := 0x384ba63473a4ba6347384ba63473a4ba6347180181f00180181f00180181f00180181f00
def t78 : Nat := 0x384ba63473a4ba634738cba63477bcba6347180181f00180181f00180181f001bc181fff
def t79 : Nat := 0x384ba63677d6bb6b57384ba63677d6bb6b57180181f00180181f00180181f00180181f00
def t80 : Nat := 0x38900842c7ff91ce1a38900842c7ff91ce1a180001f001bf801fff180001f001bf801fff
def t81 : Nat := 0x38dbae74f38dbae74f38dbae74f38dbae74f180181f00180181f00180181f00180181f00
def t82 : Nat := 0x38dbae76f7dfbbef5f38dbae76f7dfbbef5f180181f00180181f00180181f00180181f00
def t83 : Nat := 0x38dbae76f7ffbbef5f38dbae76f7ffbbef5f180181f001bf981fff180181f001bf981fff
def t84 : Nat := 0x3adfef7cf3adfef7cf3adfef7cf3adfef7cf1bff81fff1bff81fff1bff81fff1bff81fff
def t85 : Nat := 0x3c7bbef7f3c7bbef7f7dfbbef7f7dfbbef7f1c3981f001c3981f00ffffffffffffffffff
def t86 : Nat := 0x45b018c3845b018c3845b018c3845b018c38e7fe7e0ffe7fe7e0ffe7fe7e0ffe7fe7e0ff
def t87 : Nat := 0x552010810000000020552010810000000020000000000000000000000000000000000000
def t88 : Nat := 0x552010830552010830552010830552010830000000000000000000000000000000000000
def t89 : Nat := 0x556914a36556914a36556914a36556914a36000000000000000000000000000000000000
def t90 : Nat := 0x55b018c3855b018c3855b018c3855b018c38000000000000000000000000000000000000
def t91 : Nat := 0x55b018c3c57f91ce3a55b018c3c57f91ce3a00000000003f8000ff00000000003f8000ff
def t92 : Nat := 0x55b93ce7e55b93ce7e7dfb9ef3f7dfb9ef3fffffffffffffffffffffffffffffffffffff
def t93 : Nat := 0x55f91ce1a00900842c55f91ce1a00900842c000000000000000000000000000000000000
def t94 : Nat := 0x55f91ce3e55f91ce3e55f91ce3e55f91ce3e000000000000000000000000000000000000
def t95 : Nat := 0x55f91ce3e57f91ce3e55f91ce3e57f91ce3e00000000003f8000ff00000000003f8000ff
def t96 : Nat := 0x576914a36576914a36576914a36576914a3603f8000ff03f8000ff03f8000ff03f8000ff
def t97 : Nat := 0x57f91ce1a00900842c57f91ce1a00900842c03f8000ff00000000003f8000ff000000000
def t98 : Nat := 0x57f91ce1a00900842c57f91ce1a00d00842c03f8000ff00000000003f8000ff000000000
def t99 : Nat := 0x57f91ce1a00900842c57f91ce1a41900842c03f8000ff00000000003f8000ff000000000
def t100 : Nat := 0x57f91ce1a00900842c7ff91ce1a28900842c03f8000ff00000000003f8000ff000000000
def t101 : Nat := 0x57f91ce1a02900842c57f91ce1a02900842c03f8000ff00000000003f8000ff000000000
def t102 : Nat := 0x57f91ce1a10900842c57f91ce1a10900842c03f8000ff00000000003f8000ff000000000
def t103 : Nat := 0x57f91ce1e10d90c62e57f91ce1e10d90c62e03f8000ff00000000003f8000ff000000000
def t104 : Nat := 0x57f91ce3a55b018c3c57f91ce3a55b018c3c03f8000ff00000000003f8000ff000000000
def t105 : Nat := 0x57f91ce3e55f91ce3e57f91ce3e55f91ce3e03f8000ff00000000003f8000ff000000000
def t106 : Nat := 0x57f91ce3e57f91ce3e57f91ce3e57f91ce3e03f8000ff03f8000ff03f8000ff03f8000ff
def t107 : Nat := 0x57f93ce5a00902846c7ffb9ef1b28d28a52d03f8000ff00000000003f8000ff000000000
def t108 : Nat := 0x57f93ce5e10d92c66e7ffb9ef1f38db8e72f03f8000ff00000000003f8000ff000000000
def t109 : Nat := 0x69c2a214169c2a214169c2a214169c2a2141e3c67e0ffe3c67e0ffe3c67e0ffe3c67e0ff
def t110 : Nat := 0x7d20108307d20108307d20108307d2010830180001f00180001f00180001f00180001f00
def t111 : Nat := 0x7d20108307d20108307d20108307d2010830fc007ff00fc007ff00fc007ff00fc007ff00
def t112 : Nat := 0x7d6bb6b57384ba63677d6bb6b57384ba6367180181f00180181f00180181f00180181f00
def t113 : Nat := 0x7d6bb6b777d6bb6b777d6bb6b777d6bb6b77180181f00180181f00180181f00180181f00
def t114 : Nat := 0x7dfb9ef3f7dfb9ef3f14393ce7e14393ce7effffffffffffffffff1c3981f001c3981f00
def t115 : Nat := 0x7dfbbef7f7dfbbef7f7dfbbef7f7dfbbef7f180181f00180181f00180181f00180181f00
def t116 : Nat := 0x7dfbbef7f7dfbbef7f7dfbbef7f7dfbbef7fffffffffffffffffffffffffffffffffffff
def t117 : Nat := 0x7ffb9ef1b28d28a52d57f93ce5a00902846c03f8000ff00000000003f8000ff000000000
def t118 : Nat := 0x7ffbbef5b28d2aa56d7ffbbef5b28d2aa56d03f8000ff00000000003f8000ff000000000
def t119 : Nat := 0x7ffbbef5f38dbae76f7ffbbef5f38dbae76f1bf981fff180181f001bf981fff180181f00
def t120 : Nat := 0x7ffbbef7f7ffbbef7f7ffbbef7f7ffbbef7f1bf981fff1bf981fff1bf981fff1bf981fff
def t121 : Nat := 0x800000000800000000800000000800000000000000000000000000000000000000000000
def t122 : Nat := 0x800000000800000000e90000000e90000000000000000000000000e0007e000e0007e000
def t123 : Nat := 0x800000000820000000e98000000ebc000000000000000000000000e0007e000e3c07e0ff
def t124 : Nat := 0x800000020d52010810e90000020fd2010810000000000000000000e0007e000e0007e000
def t125 : Nat := 0x800020040800020040e94282101e94282101000000000000000000e0007e000e0007e000
def t126 : Nat := 0x8004410a0c724518908004410a0c72451890e4067e000e7fe7e0ffe4067e000e7fe7e0ff
def t127 : Nat := 0x8004610c08204610c0a806c3181eb46c3181000000000000000000e0067e000e3c67e0ff
def t128 : Nat := 0x8004610e4d72d75ad2a806c31a5ff6fd7b93fc07fff00ffffffffffc07fff00fffffffff
def t129 : Nat := 0x80900842cd7f91ce1ae9900842cfff91ce1a00000000003f8000ffe0007e000e3f87e0ff
def t130 : Nat := 0x820441080820441080820441080820441080000000000000000000000000000000000000
def t131 : Nat := 0x820441080820441080828441080c3c44108000000000000000000000000000003c0000ff
def t132 : Nat := 0x820441080820441080c38441080c38441080000000000000000000e3c67e0ffe3c67e0ff
def t133 : Nat := 0x820441080820441080eb0441080eb0441080000000000000000000e0007e000e0007e000
def t134 : Nat := 0x8204610c08204610c0aa06c3181eb46c3181000000000000000000e0067e000e3c67e0ff
def t135 : Nat := 0x8204610c08204610c0aa46c3181aa46c3181000000000000000000000000000000000000
def t136 : Nat := 0x8204610c08204610c0aac6c3181ebc6c318100000000000000000000000000003c0000ff
def t137 : Nat := 0x8204610c08204610c0aac6c3181ebc6c3181000000000000000000e3c67e0ffe3c67e0ff
def t138 : Nat := 0x8204610c08204610c0eb46c3181eb46c3181000000000000000000e0007e000e0007e000
def t139 : Nat := 0x8204610c08204610c0eb46c3181eb46c3181000000000000000000e3c67e0ffe3c67e0ff
def t140 : Nat := 0x8204610c08204610c0eb86c3181ebc6c3181000000000000000000e3c67e0ffe3c67e0ff
def t141 : Nat := 0x8204610c08204610c0ebc6c3181ebc6c3181000000000000000000e3c67e0ffe3c67e0ff
def t142 : Nat := 0x8204610c4924d652c2ebc6c3185fbcfc7383000000000000000000e3c67e0ffe3c67e0ff
def t143 : Nat := 0x8204610e0d724718d0ebc6c31a1ffe6d3991000000000000000000e3c67e0ffe3c67e0ff
def t144 : Nat := 0x8214694ec963d7dedaebd6cb5adffffdff9b000000000003800000e3c67e0ffe3fe7e0ff
def t145 : Nat := 0x8284610c0c3c4610c0ebc6c3181ebc6c318100000000003c0000ffe3c67e0ffe3c67e0ff
def t146 : Nat := 0x829449488829449488829449488829449488e7fe7e0ffe7fe7e0ffe7fe7e0ffe7fe7e0ff
def t147 : Nat := 0x8294494a8c7b459c988294494a8c7b459c98e7fe7e0ffe7fe7e0ffe7fe7e0ffe7fe7e0ff
def t148 : Nat := 0x8294494acd7fd5de9a8294494acd7fd5de9a00000000003f8000ff00000000003f8000ff
def t149 : Nat := 0x8294694c88294694c8ebd6cb589ebd6cb589000000000000000000e3c67e0ffe3c67e0ff
def t150 : Nat := 0x8294694ecd7fd7dedaebd6cb5adffffdff9b00000000003f8000ffe3c67e0ffe3fe7e0ff
def t151 : Nat := 0x82dfef7cf82dfef7cf82dfef7cf82dfef7cf03ff800ff03ff800ff03ff800ff03ff800ff
def t152 : Nat := 0x82dfef7cf82dfef7cfebdfef7cfebdfef7cf03ff800ff03ff800ffe3fffe0ffe3fffe0ff
def t153 : Nat := 0x963d5debe963d5debe963d5debe963d5debe1c3981f001c3981f001c3981f001c3981f00
def t154 : Nat := 0x963d7defe963d7defeffffdffbfffffdffbf1c3981f001c3981f00ffffffffffffffffff
def t155 : Nat := 0xa80000020fd2010810a80000020fd2010810fc007ff00fc007ff00fc007ff00fc007ff00
def t156 : Nat := 0xa806e31c1a806e31c1a806e31c1a806e31c1fc07fff00fc07fff00fc07fff00fc07fff00
def t157 : Nat := 0xa806e31c5aa4fe73c3a806e31c5aa4fe73c3fc07fff00ffffffffffc07fff00fffffffff
def t158 : Nat := 0xa806e31e1ef26f39d1a806e31e1ef26f39d1fc07fff00ffffffffffc07fff00fffffffff
def t159 : Nat := 0xa806e31e5ff6ff7bd3a806e31e5ff6ff7bd3fc07fff00ffffffffffc07fff00fffffffff
def t160 : Nat := 0xa806e31e5ff6ff7bd3a846e31e5ff6ff7bd3fc07fff00ffffffffffc07fff00fffffffff
def t161 : Nat := 0xa896eb5c9a896eb5c9a896eb5c9a896eb5c9fc07fff00fc07fff00fc07fff00fc07fff00
def t162 : Nat := 0xa896eb5edfffffffdba896eb5edfffffffdbfc07fff00ffffffffffc07fff00fffffffff
def t163 : Nat := 0xaa06e31e5ff6ff7bd3aa06e31e5ff6ff7bd3fc07fff00ffffffffffc07fff00fffffffff
def t164 : Nat := 0xaa06e31e5ff6ff7bd3ebc6e31e5ffeff7bd3fc07fff00fffffffffffc7ffffffffffffff
def t165 : Nat := 0xaa46c3181aa46c31818204610c08204610c0000000000000000000000000000000000000
def t166 : Nat := 0xaa46e31c1aa46e31c1aa46e31c1aa46e31c1000000000000000000000000000000000000
def t167 : Nat := 0xaa46e31c1aa46e31c1ebc6e31c1ebc6e31c1000000000000000000e3c67e0ffe3c67e0ff
def t168 : Nat := 0xaad6cb5adffffdff9b8294694ecd7fd7deda00000000003f8000ff00000000003f8000ff
def t169 : Nat := 0xaadfef7cfaadfef7cfaadfef7cfaadfef7cfffffffffffffffffffffffffffffffffffff
def t170 : Nat := 0xaadfef7effffffffdfaadfef7effffffffdfffffffffffffffffffffffffffffffffffff
def t171 : Nat := 0xb80000000b80000000f90000000f90000000180001f00180001f00f8007ff00f8007ff00
def t172 : Nat := 0xb84ba6347b84ba6347b84ba6347b84ba6347180181f00180181f00180181f00180181f00
def t173 : Nat := 0xb84ba6347b84ba6347f94ba6347f94ba6347180181f00180181f00f801fff00f801fff00
def t174 : Nat := 0xb84fe73e7ff6ff7bd7b84fe73e7ff6ff7bd7fc07fff00ffffffffffc07fff00fffffffff
def t175 : Nat := 0xba04610c0ba04610c0fbc6c3181fbc6c3181180001f00180001f00fbc67fffffbc67ffff
def t176 : Nat := 0xba4fe73c7ba4fe73c7ba4fe73c7ba4fe73c7180181f00180181f00180181f00180181f00
def t177 : Nat := 0xba4fe73c7ba4fe73c7fbcfe73c7fbcfe73c7180181f00180181f00fbc7ffffffbc7fffff
def t178 : Nat := 0xbadfef7effffffffdffbdfef7effffffffdf180181f001bf981ffffbc7ffffffbfffffff
def t179 : Nat := 0xbc3ffffffff7fffffffdfffffffffffffffffc3ffff00fffffffffffffffffffffffffff
def t180 : Nat := 0xc52010830c52010830c52010830c52010830e4007e000e4007e000e4007e000e4007e000
def t181 : Nat := 0xc52010830c52010830ed2010830ed2010830e4007e000e4007e000e4007e000e4007e000
def t182 : Nat := 0xc52010830d52010830c52010830d52010830e4007e000e4007e000e4007e000e4007e000
def t183 : Nat := 0xc724518b0c724518b0c724518b0c724518b0e7fe7e0ffe7fe7e0ffe7fe7e0ffe7fe7e0ff
def t184 : Nat := 0xc7b459cb8c7b459cb8c7b459cb8c7b459cb8e7fe7e0ffe7fe7e0ffe7fe7e0ffe7fe7e0ff
def t185 : Nat := 0xc7b459cb8d7b459cb8c7b459cb8d7b459cb8e7fe7e0ffe7fe7e0ffe7fe7e0ffe7fe7e0ff
def t186 : Nat := 0xc7b459cbcd7fd5debac7b459cbcd7fd5debae7fe7e0ffe7fe7e0ffe7fe7e0ffe7fe7e0ff
def t187 : Nat := 0xc7b479cf8c7b479cf8eff6dbdb9eff6dbdb9e7fe7e0ffe7fe7e0ffe7fe7e0ffe7fe7e0ff
def t188 : Nat := 0xc7fffffffc7fffffffc7fffffffc7fffffffe7fffe0ffe7fffe0ffe7fffe0ffe7fffe0ff
def t189 : Nat := 0xd52010830d52010830fd2010830fd2010830000000000000000000e0007e000e0007e000
def t190 : Nat := 0xd52010830d52010830fd2010830fd2010830fc007ff00fc007ff00fc007ff00fc007ff00
def t191 : Nat := 0xd724718f0d724718f0ffe6d39b1ffe6d39b1000000000000000000e3c67e0ffe3c67e0ff
def t192 : Nat := 0xd7bd7defed7bd7defeffffdffbfffffdffbfffffffffffffffffffffffffffffffffffff
def t193 : Nat := 0xd7f91ce1a80900842cd7f91ce1a80900842c03f8000ff00000000003f8000ff000000000
def t194 : Nat := 0xd7fd5de9a8294494acd7fd5de9a8294494ac03f8000ff00000000003f8000ff000000000
def t195 : Nat := 0xd7fd7deda8294694ecffffdff9baad6cb5ad03f8000ff00000000003f8000ff000000000
def t196 : Nat := 0xd7fd7deda8294694ecffffdff9bebd6cb5ad03f8000ff000000000e3fe7e0ffe3c67e0ff
def t197 : Nat := 0xd7fd7defed7fd7defeffffdffbfffffdffbf03f8000ff03f8000ffe3fe7e0ffe3fe7e0ff
def t198 : Nat := 0xe90000000e90000000800000000800000000e0007e000e0007e000000000000000000000
def t199 : Nat := 0xe90000000e90000000e90000000e90000000e0007e000e0007e000e0007e000e0007e000
def t200 : Nat := 0xeb04610c0eb04610c0ebc6c3181ebc6c3181e0007e000e0007e000e3c67e0ffe3c67e0ff
def t201 : Nat := 0xebc6c3181ebc6c31818204610c08204610c0e3c67e0ffe3c67e0ff000000000000000000
def t202 : Nat := 0xebc6c3181ebc6c31818204610c08244610c0e3c67e0ffe3c67e0ff000000000000000000
def t203 : Nat := 0xebc6c3181ebc6c31818204610c0c304610c0e3c67e0ffe3c67e0ff000000000000000000
def t204 : Nat := 0xebc6c3181ebc6c31818284610c08284610c0e3c67e0ffe3c67e0ff000000000000000000
def t205 : Nat := 0xebc6c3181ebc6c3181aa04610c0aa04610c0e3c67e0ffe3c67e0ff000000000000000000
def t206 : Nat := 0xebc6c3181fbc6c31818204610c09204610c0e3c67e0ffe3c67e0ff000000000000000000
def t207 : Nat := 0xebc6c3185fbcfc73838204610c4924d652c2e3c67e0ffe3c67e0ff000000000000000000
def t208 : Nat := 0xebc6c31a1ffe6d39918204610e0d724718d0e3c67e0ffe3c67e0ff000000000000000000
def t209 : Nat := 0xebc6c31a5ffefd7b938204610e4d76d75ad2e3c67e0ffe3c67e0ff000000000000000000
def t210 : Nat := 0xebc6e31c1ebc6e31c1aa46e31c1aa46e31c1e3c67e0ffe3c67e0ff000000000000000000
def t211 : Nat := 0xebc6e31c1ebc6e31c1ebc6e31c1ebc6e31c1e3c67e0ffe3c67e0ffe3c67e0ffe3c67e0ff
def t212 : Nat := 0xebc6e31c5fbcfe73c3aa46e31c5ba4fe73c3e3c67e0ffe3c67e0ff000000000000000000
def t213 : Nat := 0xebd6cb589ebd6cb5898294694c88294694c8e3c67e0ffe3c67e0ff000000000000000000
def t214 : Nat := 0xebd6cb58dfbdfcf78b8294694cc92dd6d6cae3c67e0ffe3c67e0ff000000000000000000
def t215 : Nat := 0xebd6cb5a9fff6dbd998294694e8d7b479cd8e3c67e0ffe3c67e0ff000000000000000000
def t216 : Nat := 0xebd6cb5adffffdff9b8214694ec963d7dedae3c67e0ffe3fe7e0ff000000000003800000
def t217 : Nat := 0xebd6cb5adffffdff9b8294694ecd7fd7dedae3c67e0ffe3fe7e0ff00000000003f8000ff
def t218 : Nat := 0xebd6eb5edfffffffdbebd6eb5edfffffffdbe3c67e0ffe3fe7e0ffe3c67e0ffe3fe7e0ff
def t219 : Nat := 0xed2010830fd2010830ed2010830fd2010830fc007ff00fc007ff00fc007ff00fc007ff00
def t220 : Nat := 0xefb6fbdfdffffffffbefb6fbdfdffffffffbffffffffffffffffffffffffffffffffffff
def t221 : Nat := 0xeff6dbdb9eff6dbdb9863479cf8863479cf8e7fe7e0ffe7fe7e0ff043800000043800000
def t222 : Nat := 0xfbcfc7383ebc6c3185924d652c28204610c4e3c67e0ffe3c67e0ff000000000000000000
def t223 : Nat := 0xfbcfc7387fbcfc7387924d652c6924d652c6e3c67e0ffe3c67e0ff000000000000000000
def t224 : Nat := 0xfbcfe73c7fbcfe73c7ba4fe73c7ba4fe73c7fbc7ffffffbc7fffff180181f00180181f00
def t225 : Nat := 0xfbcfe73c7fbcfe73c7fbcfe73c7fbcfe73c7fbc7ffffffbc7ffffffbc7ffffffbc7fffff
def t226 : Nat := 0xfd2010830fd2010830fd2010830fd2010830fc007ff00fc007ff00fc007ff00fc007ff00
def t227 : Nat := 0xfd2010830fd2010830fd2010830fd6010830fc007ff00fc007ff00fc007ff00fc007ff00
def t228 : Nat := 0xfd2010830fd2010830fda010830fda010830fc007ff00fc007ff00fc007ff00fc007ff00
def t229 : Nat := 0xfd2010830ff2010830fd2010830ff2010830fc007ff00fc007ff00fc007ff00fc007ff00
def t230 : Nat := 0xfd2010830ff2010830fda010830ffe010830fc007ff00fc007ff00fc007ff00ffc07ffff
def t231 : Nat := 0xfd2010834fd6914a32fd2010834fd6914a32fc007ff00fc007ff00fc007ff00fc007ff00
def t232 : Nat := 0xfd2030870fd2030870fd6292931fd6292931fc007ff00fc007ff00fc007ff00fc007ff00
def t233 : Nat := 0xfd2030874fd6934a72fd6292935fd6b96b33fc007ff00fc007ff00fc007ff00fc007ff00
def t234 : Nat := 0xfd22b2975fd6bb6b73fd22b2975fd6bb6b73fc01fff00fc01fff00fc01fff00fc01fff00
def t235 : Nat := 0xfd26f39f1fd26f39f1fd26f39f1fd26f39f1fc07fff00fc07fff00fc07fff00fc07fff00
def t236 : Nat := 0xfd26f39f5ff6ff7bf3fd26f39f5ff6ff7bf3fc07fff00ffffffffffc07fff00fffffffff
def t237 : Nat := 0xfd2934a76fd2934a76fd6b96b37fd6b96b37fc01fff00fc01fff00fc01fff00fc01fff00
def t238 : Nat := 0xfd393ce7efd393ce7efdfb9ef3ffdfb9ef3ffc39fff00fc39fff00ffffffffffffffffff
def t239 : Nat := 0xfd6292931fd6292931fd2030870fd2030870fc007ff00fc007ff00fc007ff00fc007ff00
def t240 : Nat := 0xfd62b2971fd62b2971fd62b2971fd62b2971fc007ff00fc007ff00fc007ff00fc007ff00
def t241 : Nat := 0xfd6914a32fd2010834fd6914a32fd2010834fc007ff00fc007ff00fc007ff00fc007ff00
def t242 : Nat := 0xfd6914a36fd6914a36fd6914a36fd6914a36fc007ff00fc007ff00fc007ff00fc007ff00
def t243 : Nat := 0xfd6bb6b77fd6bb6b77fd6bb6b77fd6bb6b77fc01fff00fc01fff00fc01fff00fc01fff00
def t244 : Nat := 0xfdb018c38fdb018c38fdb018c38fdb018c38fc007ff00fc007ff00fc007ff00fc007ff00
def t245 : Nat := 0xfdb018c3cfdf91ce3afdb018c3cfdf91ce3afc007ff00fc007ff00fc007ff00fc007ff00
def t246 : Nat := 0xfdb018c3cfff91ce3afdb018c3cfff91ce3afc007ff00fff87fffffc007ff00fff87ffff
def t247 : Nat := 0xfdfbbef7ffdfbbef7ffdfbbef7ffdfbbef7ffc01fff00fc01fff00fc01fff00fc01fff00
def t248 : Nat := 0xfdfbbef7ffffbbef7ffdfbbef7ffffbbef7ffc01fff00fff9ffffffc01fff00fff9fffff
def t249 : Nat := 0xff24518b0ff24518b0ff24518b0ff24518b0fc007ff00fc007ff00fc007ff00fc007ff00
def t250 : Nat := 0xff24718f0ff24718f0ff66d39b1ff66d39b1fc007ff00fc007ff00fc007ff00fc007ff00
def t251 : Nat := 0xff24718f0ff24718f0ffe6d39b1ffe6d39b1fc007ff00fc007ff00ffc67ffffffc67ffff
def t252 : Nat := 0xff66d39b1ff66d39b1ff24718f0ff24718f0fc007ff00fc007ff00fc007ff00fc007ff00
def t253 : Nat := 0xff6ff7bd3a806e31e5ff6ff7bd3a806e31e5ffffffffffc07fff00ffffffffffc07fff00
def t254 : Nat := 0xff6ff7bf7ff6ff7bf7ff6ff7bf7ff6ff7bf7fc01fff00fc01fff00fc01fff00fc01fff00
def t255 : Nat := 0xff6ff7bf7ff6ff7bf7ff6ff7bf7ff6ff7bf7ffffffffffffffffffffffffffffffffffff
def t256 : Nat := 0xff6ff7bf7ff6ff7bf7ffeff7bf7ffeff7bf7fc01fff00fc01fff00ffc7fffffffc7fffff
def t257 : Nat := 0xffb459cb8ffb459cb8ffb459cb8ffb459cb8fffe7fffffffe7fffffffe7fffffffe7ffff
def t258 : Nat := 0xffb479cfcfffd7defafff6dbdbdffffdffbbfc007ff00fff87ffffffc67fffffffe7ffff
def t259 : Nat := 0xffe6d3991ebc6c31a1d724718d08204610e0e3c67e0ffe3c67e0ff000000000000000000
def t260 : Nat := 0xffe6d39b1ffe6d39b1d724718f0d724718f0e3c67e0ffe3c67e0ff000000000000000000
def t261 : Nat := 0xffe6d39b1ffe6d39b1ff24718f0ff24718f0ffc67ffffffc67fffffc007ff00fc007ff00
def t262 : Nat := 0xffe6f39f1ffe6f39f1ffe6f39f1ffe6f39f1ffc67ffffffc67ffffffc67ffffffc67ffff
def t263 : Nat := 0xffefd7b93ebc6c31a5d76d75ad28204610e4e3c67e0ffe3c67e0ff000000000000000000
def t264 : Nat := 0xfff91ce3afdb018c3cfff91ce3afdb018c3cfff87fffffc007ff00fff87fffffc007ff00
def t265 : Nat := 0xfff91ce3efff91ce3efff91ce3efff91ce3efff87fffffff87fffffff87fffffff87ffff
def t266 : Nat := 0xfffbbef7ffdfbbef7ffffbbef7ffdfbbef7ffff9ffffffc01fff00fff9ffffffc01fff00
def t267 : Nat := 0xffffdff9baad6cb5add7fd7deda8294694ec03f8000ff00000000003f8000ff000000000
def t268 : Nat := 0xffffdff9bebd6cb5add7fd7deda8294694ece3fe7e0ffe3c67e0ff03f8000ff000000000
def t269 : Nat := 0xfffffffdbaad6eb5edfffffffdbaad6eb5ed03f8000ff00000000003f8000ff000000000
def t270 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def rowsE (i : Nat) : List Nat :=
  (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then [t35,t254,t269] else [t81,t94,t141,t201]) else (if i < 3 then [t106,t115,t141,t201] else [t74,t94,t141,t201])) else (if i < 6 then (if i < 5 then [t35,t107,t165,t243] else [t35,t97,t166,t243]) else (if i < 7 then [t35,t118,t130,t243] else [t35,t118,t176,t226]))) else (if i < 12 then (if i < 10 then (if i < 9 then [t35,t176,t226,t269] else [t35,t97,t166,t254]) else (if i < 11 then [t81,t106,t141,t201,t226] else [t74,t106,t141,t201,t244])) else (if i < 14 then (if i < 13 then [t35,t97,t113,t141,t201] else [t35,t97,t176,t211,t226]) else (if i < 15 then [t35,t159,t176,t211,t226] else [t35,t113,t141,t159,t201])))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then [t74,t106,t141,t201,t245] else [t83,t105,t141,t201,t243]) else (if i < 19 then [t35,t119,t141,t243,t263] else [t74,t96,t141,t201,t226])) else (if i < 22 then (if i < 21 then [t106,t141,t183,t201,t226] else [t81,t106,t141,t201,t247]) else (if i < 23 then [t81,t141,t156,t201,t226] else [t81,t88,t106,t141,t201]))) else (if i < 28 then (if i < 26 then (if i < 25 then [t60,t81,t106,t141,t226] else [t46,t81,t106,t141,t201]) else (if i < 27 then [t81,t106,t141,t213,t226] else [t81,t106,t141,t201,t244])) else (if i < 30 then (if i < 29 then [t81,t106,t141,t201,t243] else [t74,t106,t141,t201,t247]) else (if i < 31 then [t74,t106,t149,t213,t226] else [t74,t106,t141,t213,t244]))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then [t106,t141,t184,t201,t244] else [t74,t141,t156,t201,t244]) else (if i < 35 then [t74,t90,t106,t141,t201] else [t60,t74,t106,t141,t244])) else (if i < 38 then (if i < 37 then [t40,t74,t106,t141,t201] else [t26,t74,t89,t141,t201]) else (if i < 39 then [t74,t141,t161,t201,t226] else [t26,t106,t113,t141,t201]))) else (if i < 44 then (if i < 42 then (if i < 41 then [t82,t106,t141,t201,t226] else [t74,t91,t104,t141,t201]) else (if i < 43 then [t35,t104,t113,t141,t201] else [t35,t97,t141,t146,t201])) else (if i < 46 then (if i < 45 then [t35,t60,t97,t113,t141] else [t35,t97,t113,t141,t260]) else (if i < 47 then [t35,t74,t97,t191,t260] else [t35,t97,t106,t176,t211,t226])))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then [t74,t148,t196,t226,t268] else [t35,t176,t196,t226,t268]) else (if i < 51 then [t35,t74,t196,t249,t268] else [t35,t97,t176,t218,t226])) else (if i < 54 then (if i < 53 then [t74,t95,t141,t201,t264] else [t35,t104,t112,t141,t201]) else (if i < 55 then [t35,t107,t177,t201,t243] else [t35,t74,t107,t165,t226]))) else (if i < 60 then (if i < 58 then (if i < 57 then [t35,t97,t167,t224,t243] else [t35,t74,t97,t166,t226]) else (if i < 59 then [t15,t35,t97,t165,t243] else [t74,t141,t168,t226,t267])) else (if i < 62 then (if i < 61 then [t35,t141,t176,t226,t267] else [t35,t74,t141,t252,t267]) else (if i < 63 then [t35,t97,t167,t176,t226] else [t35,t107,t176,t201,t226])))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then [t74,t95,t141,t201,t266] else [t13,t74,t93,t141,t201]) else (if i < 67 then [t35,t118,t141,t201,t243] else [t35,t68,t97,t130,t243])) else (if i < 70 then (if i < 69 then [t35,t97,t176,t211,t243] else [t35,t74,t118,t130,t226]) else (if i < 71 then [t35,t68,t97,t176,t226] else [t74,t148,t194,t211,t226]))) else (if i < 76 then (if i < 74 then (if i < 73 then [t35,t176,t194,t211,t226] else [t35,t74,t194,t211,t249]) else (if i < 75 then [t35,t86,t97,t211,t226] else [t35,t97,t166,t176,t226])) else (if i < 78 then (if i < 77 then [t35,t97,t176,t211,t254] else [t35,t58,t97,t176,t226]) else (if i < 79 then [t35,t46,t97,t176,t211] else [t35,t97,t176,t211,t249])))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then [t35,t74,t97,t109,t226] else [t35,t74,t97,t153,t226]) else (if i < 83 then [t35,t74,t97,t141,t201,t226] else [t35,t74,t141,t159,t201,t226])) else (if i < 86 then (if i < 85 then [t35,t97,t141,t184,t201,t226] else [t35,t74,t97,t141,t201,t243]) else (if i < 87 then [t35,t60,t74,t97,t141,t226] else [t35,t46,t74,t97,t141,t201]))) else (if i < 92 then (if i < 90 then (if i < 89 then [t74,t141,t159,t201,t226,t253] else [t35,t141,t159,t184,t201,t226]) else (if i < 91 then [t35,t74,t141,t159,t201,t243] else [t35,t60,t74,t141,t159,t226])) else (if i < 94 then (if i < 93 then [t35,t46,t74,t141,t159,t201] else [t35,t83,t97,t141,t201,t243]) else (if i < 95 then [t35,t74,t103,t141,t201,t226] else [t35,t74,t97,t141,t207,t226]))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then [t35,t74,t97,t141,t201,t231] else [t26,t74,t106,t141,t201,t226]) else (if i < 99 then [t35,t74,t88,t97,t141,t201] else [t35,t81,t97,t141,t201,t226])) else (if i < 102 then (if i < 101 then [t35,t74,t97,t141,t213,t226] else [t35,t74,t97,t141,t201,t244]) else (if i < 103 then [t35,t79,t97,t141,t201,t226] else [t35,t74,t104,t141,t201,t226]))) else (if i < 108 then (if i < 106 then (if i < 105 then [t35,t74,t97,t141,t208,t226] else [t35,t60,t97,t141,t184,t226]) else (if i < 107 then [t35,t97,t141,t180,t184,t201] else [t35,t46,t97,t141,t184,t201])) else (if i < 110 then (if i < 109 then [t35,t97,t141,t184,t201,t243] else [t35,t74,t97,t141,t180,t201]) else (if i < 111 then [t35,t74,t97,t135,t201,t226] else [t35,t74,t107,t141,t201,t226])))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then [t35,t74,t97,t141,t210,t226] else [t35,t74,t97,t141,t201,t232]) else (if i < 115 then [t35,t60,t74,t97,t141,t243] else [t35,t42,t74,t97,t141,t201])) else (if i < 118 then (if i < 117 then [t35,t60,t74,t97,t114,t226] else [t35,t46,t60,t74,t97,t141]) else (if i < 119 then [t35,t74,t97,t130,t211,t226] else [t35,t74,t141,t194,t201,t226]))) else (if i < 124 then (if i < 122 then (if i < 121 then [t35,t97,t141,t176,t201,t226] else [t35,t74,t97,t141,t201,t249]) else (if i < 123 then [t35,t74,t84,t97,t141,t201] else [t141,t159,t184,t201,t226,t253])) else (if i < 126 then (if i < 125 then [t74,t141,t159,t201,t243,t253] else [t60,t74,t141,t159,t226,t253]) else (if i < 127 then [t46,t74,t141,t159,t201,t253] else [t35,t83,t141,t159,t201,t243]))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then [t35,t74,t141,t159,t207,t226] else [t35,t74,t141,t159,t201,t231]) else (if i < 131 then [t14,t74,t141,t162,t201,t226] else [t35,t79,t141,t159,t201,t226])) else (if i < 134 then (if i < 133 then [t35,t74,t141,t159,t208,t226] else [t35,t60,t141,t159,t184,t226]) else (if i < 135 then [t35,t141,t159,t180,t184,t201] else [t35,t46,t141,t159,t184,t201]))) else (if i < 140 then (if i < 138 then (if i < 137 then [t35,t141,t159,t184,t201,t243] else [t35,t74,t141,t159,t180,t201]) else (if i < 139 then [t35,t74,t135,t159,t201,t226] else [t36,t74,t141,t159,t201,t226])) else (if i < 142 then (if i < 141 then [t35,t74,t141,t160,t201,t226] else [t35,t74,t141,t159,t210,t226]) else (if i < 143 then [t35,t74,t141,t159,t201,t232] else [t35,t66,t141,t174,t201,t226])))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then [t35,t74,t141,t159,t201,t234] else [t35,t66,t141,t159,t201,t243]) else (if i < 147 then [t35,t60,t74,t141,t159,t243] else [t35,t42,t74,t141,t159,t201])) else (if i < 150 then (if i < 149 then [t35,t60,t74,t114,t159,t226] else [t35,t46,t60,t74,t141,t159]) else (if i < 151 then [t35,t74,t127,t164,t201,t226] else [t35,t74,t134,t159,t201,t226]))) else (if i < 156 then (if i < 154 then (if i < 153 then [t35,t74,t130,t159,t211,t226] else [t74,t141,t148,t159,t201,t226]) else (if i < 155 then [t35,t141,t159,t176,t201,t226] else [t35,t74,t141,t163,t201,t226])) else (if i < 158 then (if i < 157 then [t35,t74,t141,t159,t201,t249] else [t35,t74,t141,t155,t201,t236]) else (if i < 159 then [t35,t74,t84,t141,t159,t201] else [t35,t74,t88,t141,t159,t201]))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then [t35,t81,t141,t159,t201,t226] else [t35,t74,t141,t159,t213,t226]) else (if i < 163 then [t35,t74,t141,t159,t201,t244] else [t35,t119,t141,t159,t201,t243])) else (if i < 166 then (if i < 165 then [t55,t74,t141,t159,t201,t226] else [t35,t74,t141,t159,t222,t226]) else (if i < 167 then [t35,t74,t141,t159,t201,t241] else [t35,t74,t97,t141,t201,t234]))) else (if i < 172 then (if i < 170 then (if i < 169 then [t35,t66,t97,t141,t201,t243] else [t35,t112,t141,t159,t201,t226]) else (if i < 171 then [t74,t91,t141,t159,t201,t226] else [t35,t74,t141,t159,t226,t259])) else (if i < 174 then (if i < 173 then [t35,t74,t97,t134,t201,t226] else [t35,t83,t103,t141,t201,t226]) else (if i < 175 then [t35,t83,t97,t141,t201,t231] else [t55,t74,t119,t141,t201,t226])))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then [t35,t74,t119,t141,t222,t226] else [t83,t106,t119,t141,t201,t226]) else (if i < 179 then [t29,t74,t106,t141,t201,t226] else [t35,t106,t119,t141,t201,t243])) else (if i < 182 then (if i < 181 then [t35,t119,t141,t196,t201,t243] else [t13,t83,t97,t141,t201,t243]) else (if i < 183 then [t35,t97,t126,t141,t201,t243] else [t35,t97,t120,t141,t201,t243]))) else (if i < 188 then (if i < 186 then (if i < 185 then [t35,t79,t97,t141,t201,t243] else [t35,t60,t83,t97,t141,t243]) else (if i < 187 then [t35,t42,t83,t97,t141,t201] else [t35,t74,t97,t110,t141,t201])) else (if i < 190 then (if i < 189 then [t35,t74,t97,t141,t214,t226] else [t35,t74,t97,t141,t201,t245]) else (if i < 191 then [t35,t74,t97,t136,t201,t226] else [t32,t74,t97,t141,t201,t226])))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then [t35,t74,t97,t140,t201,t226] else [t35,t74,t97,t141,t201,t219]) else (if i < 195 then [t35,t103,t141,t184,t201,t226] else [t35,t74,t103,t141,t201,t243])) else (if i < 198 then (if i < 197 then [t35,t74,t141,t158,t201,t226] else [t35,t60,t74,t103,t141,t226]) else (if i < 199 then [t35,t46,t74,t103,t141,t201] else [t35,t74,t103,t141,t207,t226]))) else (if i < 204 then (if i < 202 then (if i < 201 then [t35,t74,t103,t141,t201,t231] else [t35,t97,t141,t184,t207,t226]) else (if i < 203 then [t35,t74,t97,t141,t207,t243] else [t35,t60,t74,t97,t142,t226])) else (if i < 206 then (if i < 205 then [t35,t51,t74,t97,t141,t226] else [t35,t46,t74,t97,t141,t207]) else (if i < 207 then [t35,t74,t97,t142,t207,t226] else [t35,t74,t97,t141,t207,t231])))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then [t35,t74,t98,t141,t201,t226] else [t35,t74,t97,t141,t202,t226]) else (if i < 211 then [t35,t74,t97,t141,t201,t227] else [t35,t97,t141,t184,t201,t231])) else (if i < 214 then (if i < 213 then [t35,t60,t74,t97,t141,t231] else [t35,t43,t74,t97,t141,t201]) else (if i < 215 then [t35,t74,t102,t141,t201,t226] else [t35,t74,t97,t141,t206,t226]))) else (if i < 220 then (if i < 218 then (if i < 217 then [t35,t61,t74,t97,t141,t226] else [t35,t48,t74,t97,t141,t201]) else (if i < 219 then [t74,t106,t141,t201,t226,t255] else [t81,t106,t141,t201,t226])) else (if i < 222 then (if i < 221 then [t26,t81,t106,t141,t201,t226] else [t74,t81,t106,t141,t201,t226]) else (if i < 223 then [t26,t74,t106,t141,t213,t226] else [t74,t106,t141,t201,t244]))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then [t26,t74,t106,t141,t201,t244] else [t74,t106,t141,t201,t226,t244]) else (if i < 227 then [t26,t106,t141,t184,t201,t226] else [t26,t74,t106,t141,t201,t243])) else (if i < 230 then (if i < 229 then [t26,t74,t141,t156,t201,t226] else [t26,t74,t88,t106,t141,t201]) else (if i < 231 then [t26,t60,t74,t106,t141,t226] else [t26,t46,t74,t106,t141,t201]))) else (if i < 236 then (if i < 234 then (if i < 233 then [t35,t81,t106,t141,t201,t226] else [t35,t74,t106,t141,t201,t244]) else (if i < 235 then [t74,t106,t141,t201,t246,t264] else [t31,t74,t106,t141,t201,t226])) else (if i < 238 then (if i < 237 then [t35,t88,t97,t141,t184,t201] else [t35,t74,t97,t141,t223,t226]) else (if i < 239 then [t35,t74,t97,t141,t201,t242] else [t35,t74,t97,t106,t135,t201,t226])))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then [t35,t74,t89,t97,t141,t201] else [t35,t74,t97,t141,t201,t235]) else (if i < 243 then [t35,t74,t97,t141,t189,t201] else [t35,t74,t88,t104,t141,t201])) else (if i < 246 then (if i < 245 then [t35,t97,t113,t141,t201] else [t35,t74,t97,t113,t141,t201]) else (if i < 247 then [t35,t88,t97,t113,t141,t201] else [t35,t74,t97,t141,t169,t201]))) else (if i < 252 then (if i < 250 then (if i < 249 then [t35,t74,t88,t97,t141,t260] else [t35,t60,t74,t88,t97,t141]) else (if i < 251 then [t35,t97,t106,t113,t141,t201] else [t35,t97,t113,t141,t201,t226])) else (if i < 254 then (if i < 253 then [t35,t74,t97,t141,t226,t260] else [t35,t74,t97,t106,t130,t211,t226]) else (if i < 255 then [t35,t97,t106,t141,t176,t201,t226] else [t35,t45,t74,t97,t141,t201])))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then [t35,t74,t97,t139,t201,t226] else [t35,t97,t141,t183,t201,t226]) else (if i < 259 then [t35,t81,t97,t141,t201,t247] else [t35,t60,t81,t97,t141,t226])) else (if i < 262 then (if i < 261 then [t35,t46,t81,t97,t141,t201] else [t35,t81,t97,t141,t213,t226]) else (if i < 263 then [t35,t81,t97,t141,t201,t244] else [t35,t81,t97,t141,t201,t243]))) else (if i < 268 then (if i < 266 then (if i < 265 then [t35,t74,t97,t141,t201,t247] else [t35,t97,t141,t184,t213,t226]) else (if i < 267 then [t35,t74,t97,t141,t213,t243] else [t35,t60,t74,t97,t149,t226])) else (if i < 270 then (if i < 269 then [t35,t57,t74,t97,t141,t226] else [t35,t46,t74,t97,t141,t213]) else (if i < 271 then [t35,t74,t97,t149,t213,t226] else [t35,t74,t97,t141,t213,t244])))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then [t35,t76,t97,t141,t201,t226] else [t35,t74,t97,t141,t204,t226]) else (if i < 275 then [t35,t74,t97,t141,t201,t228] else [t35,t97,t141,t184,t201,t244])) else (if i < 278 then (if i < 277 then [t35,t60,t74,t97,t141,t244] else [t35,t40,t74,t97,t141,t201]) else (if i < 279 then [t35,t63,t74,t97,t141,t226] else [t35,t74,t130,t196,t226,t268]))) else (if i < 284 then (if i < 282 then (if i < 281 then [t35,t74,t97,t135,t217,t226] else [t35,t74,t108,t141,t201,t226]) else (if i < 283 then [t35,t74,t97,t141,t212,t226] else [t35,t74,t97,t141,t201,t233])) else (if i < 286 then (if i < 285 then [t35,t97,t141,t176,t217,t226] else [t35,t74,t141,t194,t217,t226]) else (if i < 287 then [t35,t74,t97,t141,t217,t249] else [t35,t74,t97,t130,t218,t226]))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then [t35,t78,t97,t141,t201,t243] else [t35,t77,t97,t141,t201,t226]) else (if i < 291 then [t35,t74,t101,t141,t201,t226] else [t35,t74,t97,t141,t201,t229])) else (if i < 294 then (if i < 293 then [t35,t75,t97,t141,t201,t226] else [t35,t74,t99,t141,t201,t226]) else (if i < 295 then [t35,t74,t97,t141,t203,t226] else [t35,t79,t97,t141,t201,t246]))) else (if i < 300 then (if i < 298 then (if i < 297 then [t35,t74,t104,t141,t201,t246] else [t74,t91,t141,t201,t226,t264]) else (if i < 299 then [t13,t74,t97,t141,t201,t246] else [t35,t82,t97,t141,t201,t226])) else (if i < 302 then (if i < 301 then [t35,t74,t97,t141,t215,t226] else [t35,t69,t97,t141,t201,t226]) else (if i < 303 then [t35,t74,t97,t137,t201,t226] else [t35,t97,t141,t147,t201,t226])))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then [t11,t35,t97,t112,t141,t201] else [t35,t60,t79,t97,t141,t226]) else (if i < 307 then [t35,t46,t79,t97,t141,t201] else [t35,t79,t104,t141,t201,t226])) else (if i < 310 then (if i < 309 then [t35,t79,t97,t141,t208,t226] else [t35,t104,t141,t184,t201,t226]) else (if i < 311 then [t35,t74,t104,t141,t201,t243] else [t35,t74,t141,t157,t201,t226]))) else (if i < 316 then (if i < 314 then (if i < 313 then [t35,t60,t74,t104,t141,t226] else [t35,t46,t74,t104,t141,t201]) else (if i < 315 then [t35,t74,t104,t141,t208,t226] else [t11,t74,t91,t97,t141,t201])) else (if i < 318 then (if i < 317 then [t35,t97,t141,t184,t208,t226] else [t35,t74,t97,t141,t208,t243]) else (if i < 319 then [t35,t60,t74,t97,t143,t226] else [t23,t35,t74,t97,t141,t226])))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then [t35,t46,t74,t97,t141,t208] else [t35,t74,t97,t143,t208,t226]) else (if i < 323 then [t35,t97,t141,t185,t201,t226] else [t35,t62,t74,t97,t141,t226])) else (if i < 326 then (if i < 325 then [t30,t97,t141,t186,t201,t226] else [t35,t97,t141,t182,t184,t201]) else (if i < 327 then [t35,t60,t97,t114,t184,t226] else [t35,t60,t97,t141,t180,t184]))) else (if i < 332 then (if i < 330 then (if i < 329 then [t35,t46,t60,t97,t141,t184] else [t35,t97,t132,t187,t201,t226]) else (if i < 331 then [t35,t97,t141,t181,t184,t201] else [t35,t97,t130,t184,t211,t226])) else (if i < 334 then (if i < 333 then [t35,t141,t184,t194,t201,t226] else [t35,t97,t141,t184,t201,t249]) else (if i < 335 then [t35,t97,t141,t180,t201,t257] else [t35,t84,t97,t141,t184,t201])))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then [t35,t42,t97,t141,t184,t201] else [t35,t97,t141,t186,t201,t243]) else (if i < 339 then [t35,t74,t97,t141,t182,t201] else [t35,t97,t135,t184,t201,t226])) else (if i < 342 then (if i < 341 then [t35,t107,t141,t184,t201,t226] else [t35,t97,t141,t184,t210,t226]) else (if i < 343 then [t35,t97,t141,t184,t201,t232] else [t35,t60,t97,t141,t184,t243]))) else (if i < 348 then (if i < 346 then (if i < 345 then [t35,t97,t141,t180,t201,t243] else [t35,t60,t74,t97,t141,t180]) else (if i < 347 then [t35,t74,t97,t141,t181,t201] else [t35,t74,t107,t177,t201,t226])) else (if i < 350 then (if i < 349 then [t35,t74,t97,t167,t224,t226] else [t15,t35,t97,t177,t201,t243]) else (if i < 351 then [t15,t35,t74,t97,t165,t226] else [t35,t97,t141,t177,t210,t226]))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then [t35,t97,t177,t211,t224,t226] else [t35,t74,t97,t135,t201,t243]) else (if i < 355 then [t35,t60,t74,t97,t135,t226] else [t35,t74,t97,t135,t211,t226])) else (if i < 358 then (if i < 357 then [t35,t74,t97,t141,t221,t226] else [t35,t74,t135,t195,t201,t226]) else (if i < 359 then [t35,t97,t135,t176,t201,t226] else [t35,t74,t92,t97,t141,t226]))) else (if i < 364 then (if i < 362 then (if i < 361 then [t35,t74,t97,t135,t210,t226] else [t35,t74,t97,t135,t201,t250]) else (if i < 363 then [t35,t46,t74,t97,t135,t201] else [t35,t74,t141,t195,t201,t226])) else (if i < 366 then (if i < 365 then [t35,t74,t97,t141,t201,t250] else [t35,t74,t97,t138,t201,t226]) else (if i < 367 then [t35,t53,t74,t97,t141,t226] else [t34,t74,t97,t141,t201,t226])))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then [t35,t74,t97,t141,t190,t201] else [t35,t74,t107,t141,t201,t243]) else (if i < 371 then [t35,t74,t128,t141,t201,t226] else [t35,t60,t74,t117,t141,t226])) else (if i < 374 then (if i < 373 then [t35,t74,t107,t130,t201,t226] else [t35,t60,t74,t107,t141,t226]) else (if i < 375 then [t35,t46,t74,t107,t141,t201] else [t36,t74,t107,t141,t201,t226]))) else (if i < 380 then (if i < 378 then (if i < 377 then [t35,t74,t107,t141,t210,t226] else [t35,t74,t107,t141,t201,t232]) else (if i < 379 then [t35,t74,t97,t141,t210,t243] else [t35,t60,t74,t97,t167,t226])) else (if i < 382 then (if i < 381 then [t35,t59,t74,t97,t141,t226] else [t35,t46,t74,t97,t141,t210]) else (if i < 383 then [t35,t74,t97,t141,t210,t232] else [t35,t74,t97,t130,t167,t226]))))))) else (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then [t35,t60,t74,t97,t141,t239] else [t35,t60,t74,t97,t141,t232]) else (if i < 387 then [t35,t44,t74,t97,t141,t201] else [t35,t74,t100,t141,t201,t226])) else (if i < 390 then (if i < 389 then [t35,t74,t97,t141,t205,t226] else [t15,t35,t97,t176,t201,t226]) else (if i < 391 then [t35,t47,t74,t97,t141,t201] else [t13,t74,t97,t141,t201,t248]))) else (if i < 396 then (if i < 394 then (if i < 393 then [t32,t74,t97,t141,t201,t243] else [t35,t74,t105,t141,t201,t243]) else (if i < 395 then [t35,t74,t97,t141,t209,t243] else [t35,t60,t74,t97,t114,t243])) else (if i < 398 then (if i < 397 then [t35,t42,t60,t74,t97,t141] else [t35,t68,t97,t141,t201,t243]) else (if i < 399 then [t35,t74,t97,t130,t211,t243] else [t35,t74,t141,t194,t201,t243])))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then [t35,t97,t141,t176,t201,t243] else [t35,t74,t97,t141,t201,t254]) else (if i < 403 then [t35,t74,t97,t138,t201,t243] else [t35,t42,t84,t97,t141,t201])) else (if i < 406 then (if i < 405 then [t35,t84,t97,t141,t201,t243] else [t35,t74,t105,t141,t201,t226]) else (if i < 407 then [t35,t74,t97,t141,t209,t226] else [t21,t64,t74,t97,t141,t226]))) else (if i < 412 then (if i < 410 then (if i < 409 then [t35,t60,t74,t97,t144,t226] else [t35,t52,t85,t97,t141,t226]) else (if i < 411 then [t35,t60,t74,t97,t141,t237] else [t16,t35,t74,t97,t154,t226])) else (if i < 414 then (if i < 413 then [t35,t56,t74,t97,t141,t238] else [t35,t46,t60,t74,t97,t114]) else (if i < 415 then [t35,t60,t74,t84,t97,t141] else [t35,t74,t97,t141,t216,t226]))))) else (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then [t35,t74,t97,t141,t201,t237] else [t35,t60,t74,t141,t194,t226]) else (if i < 419 then [t35,t60,t97,t141,t176,t226] else [t35,t60,t74,t97,t141,t249])) else (if i < 422 then (if i < 421 then [t35,t74,t118,t141,t201,t226] else [t35,t74,t97,t141,t201,t240]) else (if i < 423 then [t35,t68,t74,t97,t130,t226] else [t35,t74,t130,t194,t211,t226]))) else (if i < 428 then (if i < 426 then (if i < 425 then [t35,t97,t176,t211,t226] else [t35,t74,t97,t176,t211,t226]) else (if i < 427 then [t35,t97,t130,t176,t211,t226] else [t35,t74,t97,t116,t211,t226])) else (if i < 430 then (if i < 429 then [t35,t74,t97,t130,t211,t249] else [t35,t58,t74,t97,t130,t226]) else (if i < 431 then [t35,t46,t74,t97,t130,t211] else [t35,t97,t141,t176,t211,t226])))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then [t35,t67,t74,t141,t201,t226] else [t35,t46,t74,t141,t194,t201]) else (if i < 435 then [t74,t141,t148,t194,t201,t226] else [t35,t141,t176,t194,t201,t226])) else (if i < 438 then (if i < 437 then [t35,t74,t141,t194,t201,t249] else [t35,t86,t97,t141,t201,t226]) else (if i < 439 then [t35,t97,t141,t176,t201,t254] else [t35,t46,t97,t141,t176,t201]))) else (if i < 444 then (if i < 442 then (if i < 441 then [t35,t97,t141,t176,t201,t249] else [t33,t74,t97,t141,t201,t226]) else (if i < 443 then [t35,t74,t97,t111,t141,t201] else [t35,t37,t74,t97,t141,t201])) else (if i < 446 then (if i < 445 then [t35,t74,t141,t193,t201,t226] else [t35,t97,t141,t172,t201,t226]) else (if i < 447 then [t35,t74,t97,t141,t151,t201] else [t28,t49,t74,t97,t141,t201])))))) else (if i < 480 then (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then [t24,t35,t84,t97,t141,t201] else [t35,t39,t74,t97,t152,t201]) else (if i < 451 then [t35,t74,t97,t141,t201,t226] else [t35,t35,t74,t97,t141,t201,t226])) else (if i < 454 then (if i < 453 then [t35,t74,t141,t159,t201,t226] else [t35,t74,t97,t141,t159,t201,t226]) else (if i < 455 then [t35,t74,t83,t97,t141,t201,t226] else [t9,t35,t74,t97,t141,t201,t226]))) else (if i < 460 then (if i < 458 then (if i < 457 then [t35,t74,t97,t106,t141,t201,t226] else [t26,t35,t74,t97,t141,t201,t226]) else (if i < 459 then [t35,t74,t97,t141,t150,t201,t226] else [t7,t35,t74,t97,t141,t201,t226])) else (if i < 462 then (if i < 461 then [t35,t74,t97,t141,t201,t226,t246] else [t11,t35,t74,t97,t141,t201,t226]) else (if i < 463 then [t35,t74,t74,t97,t141,t201,t226] else [t35,t97,t141,t184,t201,t226])))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then [t35,t74,t97,t141,t184,t201,t226] else [t35,t74,t97,t141,t177,t201,t226]) else (if i < 467 then [t15,t35,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t201,t243])) else (if i < 470 then (if i < 469 then [t35,t74,t97,t141,t201,t226,t243] else [t35,t70,t74,t97,t141,t201,t226]) else (if i < 471 then [t35,t74,t97,t141,t141,t201,t226] else [t35,t60,t74,t97,t141,t226]))) else (if i < 476 then (if i < 474 then (if i < 473 then [t35,t60,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t201,t211,t226]) else (if i < 475 then [t35,t74,t97,t130,t141,t201,t226] else [t35,t74,t97,t141,t201,t226,t251])) else (if i < 478 then (if i < 477 then [t35,t74,t97,t122,t141,t201,t226] else [t35,t74,t97,t141,t201,t226,t226]) else (if i < 479 then [t35,t46,t74,t97,t141,t201] else [t35,t46,t74,t97,t141,t201,t226]))))) else (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then [t35,t35,t97,t141,t184,t201,t226] else [t35,t35,t74,t97,t141,t201,t243]) else (if i < 483 then [t35,t35,t74,t141,t159,t201,t226] else [t35,t35,t60,t74,t97,t141,t226])) else (if i < 486 then (if i < 485 then [t35,t35,t46,t74,t97,t141,t201] else [t74,t141,t159,t201,t226,t253]) else (if i < 487 then [t35,t74,t141,t159,t201,t226,t253] else [t35,t74,t83,t141,t159,t201,t226]))) else (if i < 492 then (if i < 490 then (if i < 489 then [t9,t35,t74,t141,t159,t201,t226] else [t35,t74,t141,t150,t159,t201,t226]) else (if i < 491 then [t7,t35,t74,t141,t159,t201,t226] else [t35,t74,t141,t159,t162,t201,t226])) else (if i < 494 then (if i < 493 then [t14,t35,t74,t141,t159,t201,t226] else [t35,t74,t141,t159,t201,t226,t246]) else (if i < 495 then [t11,t35,t74,t141,t159,t201,t226] else [t35,t74,t74,t141,t159,t201,t226])))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then [t35,t141,t159,t184,t201,t226] else [t35,t74,t141,t159,t184,t201,t226]) else (if i < 499 then [t35,t74,t141,t159,t177,t201,t226] else [t15,t35,t74,t141,t159,t201,t226])) else (if i < 502 then (if i < 501 then [t35,t74,t141,t159,t174,t201,t226] else [t35,t66,t74,t141,t159,t201,t226]) else (if i < 503 then [t35,t74,t141,t159,t201,t243] else [t35,t74,t141,t159,t201,t226,t243]))) else (if i < 508 then (if i < 506 then (if i < 505 then [t35,t70,t74,t141,t159,t201,t226] else [t35,t74,t141,t141,t159,t201,t226]) else (if i < 507 then [t35,t60,t74,t141,t159,t226] else [t35,t60,t74,t141,t159,t201,t226])) else (if i < 510 then (if i < 509 then [t35,t74,t141,t159,t164,t201,t226] else [t35,t74,t127,t141,t159,t201,t226]) else (if i < 511 then [t35,t74,t141,t159,t201,t211,t226] else [t35,t74,t130,t141,t159,t201,t226]))))))))) else (if i < 768 then (if i < 640 then (if i < 576 then (if i < 544 then (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then [t35,t74,t141,t159,t201,t226,t251] else [t35,t74,t122,t141,t159,t201,t226]) else (if i < 515 then [t35,t74,t141,t159,t159,t201,t226] else [t35,t74,t141,t159,t201,t226,t236])) else (if i < 518 then (if i < 517 then [t35,t74,t141,t155,t159,t201,t226] else [t35,t74,t141,t159,t201,t226,t226]) else (if i < 519 then [t35,t46,t74,t141,t159,t201] else [t35,t46,t74,t141,t159,t201,t226]))) else (if i < 524 then (if i < 522 then (if i < 521 then [t35,t74,t106,t141,t159,t201,t226] else [t26,t35,t74,t141,t159,t201,t226]) else (if i < 523 then [t35,t74,t97,t141,t162,t201,t226] else [t14,t35,t74,t97,t141,t201,t226])) else (if i < 526 then (if i < 525 then [t35,t97,t141,t159,t184,t201,t226] else [t35,t74,t119,t141,t159,t201,t226]) else (if i < 527 then [t9,t74,t97,t141,t201,t226,t253] else [t35,t74,t97,t141,t174,t201,t226])))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then [t35,t66,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t159,t201,t243]) else (if i < 531 then [t35,t74,t141,t159,t196,t201,t226] else [t7,t74,t97,t141,t201,t226,t253])) else (if i < 534 then (if i < 533 then [t35,t74,t97,t141,t201,t226,t270] else [t35,t74,t141,t159,t201,t226,t270]) else (if i < 535 then [t1,t35,t74,t97,t141,t201,t226] else [t1,t35,t74,t141,t159,t201,t226]))) else (if i < 540 then (if i < 538 then (if i < 537 then [t35,t74,t141,t159,t201,t226,t264] else [t11,t74,t97,t141,t201,t226,t253]) else (if i < 539 then [t35,t60,t74,t97,t141,t159,t226] else [t35,t74,t97,t141,t164,t201,t226])) else (if i < 542 then (if i < 541 then [t35,t74,t97,t127,t141,t201,t226] else [t35,t74,t97,t141,t201,t226,t236]) else (if i < 543 then [t35,t74,t97,t141,t155,t201,t226] else [t35,t46,t74,t97,t141,t159,t201]))))) else (if i < 560 then (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then [t9,t35,t83,t97,t141,t201,t226] else [t9,t74,t83,t97,t141,t201,t226]) else (if i < 547 then [t35,t74,t106,t119,t141,t201,t226] else [t35,t74,t119,t141,t196,t201,t226])) else (if i < 550 then (if i < 549 then [t35,t83,t97,t141,t184,t201,t226] else [t35,t83,t97,t119,t141,t201,t226]) else (if i < 551 then [t35,t83,t97,t141,t201,t243] else [t35,t74,t83,t97,t141,t201,t243]))) else (if i < 556 then (if i < 554 then (if i < 553 then [t35,t83,t97,t141,t201,t226,t243] else [t35,t74,t97,t126,t141,t201,t226]) else (if i < 555 then [t35,t74,t97,t120,t141,t201,t226] else [t29,t35,t74,t97,t141,t201,t226])) else (if i < 558 then (if i < 557 then [t35,t74,t97,t141,t178,t201,t226] else [t17,t35,t74,t97,t141,t201,t226]) else (if i < 559 then [t35,t74,t97,t141,t201,t226,t248] else [t35,t72,t74,t97,t141,t201,t226])))) else (if i < 568 then (if i < 564 then (if i < 562 then (if i < 561 then [t35,t60,t74,t83,t97,t141,t226] else [t35,t46,t74,t83,t97,t141,t201]) else (if i < 563 then [t35,t74,t97,t141,t201,t220,t226] else [t35,t74,t103,t141,t201,t226])) else (if i < 566 then (if i < 565 then [t9,t35,t74,t103,t141,t201,t226] else [t35,t55,t74,t97,t141,t201,t226]) else (if i < 567 then [t35,t74,t97,t141,t207,t226] else [t9,t35,t74,t97,t141,t207,t226]))) else (if i < 572 then (if i < 570 then (if i < 569 then [t35,t74,t97,t141,t142,t201,t226] else [t2,t35,t74,t97,t141,t201,t226]) else (if i < 571 then [t35,t74,t97,t141,t201,t231] else [t9,t35,t74,t97,t141,t201,t231])) else (if i < 574 then (if i < 573 then [t35,t74,t97,t141,t201,t226,t231] else [t8,t35,t74,t97,t141,t201,t226]) else (if i < 575 then [t9,t35,t97,t141,t184,t201,t226] else [t9,t35,t74,t97,t141,t201,t243])))))) else (if i < 608 then (if i < 592 then (if i < 584 then (if i < 580 then (if i < 578 then (if i < 577 then [t9,t35,t60,t74,t97,t141,t226] else [t9,t35,t46,t74,t97,t141,t201]) else (if i < 579 then [t26,t74,t106,t141,t201,t226] else [t26,t35,t74,t106,t141,t201,t226])) else (if i < 582 then (if i < 581 then [t35,t74,t106,t141,t201,t226,t264] else [t35,t97,t106,t141,t184,t201,t226]) else (if i < 583 then [t35,t54,t74,t97,t141,t201,t226] else [t35,t74,t97,t106,t141,t177,t201,t226]))) else (if i < 588 then (if i < 586 then (if i < 585 then [t35,t74,t97,t106,t141,t201,t243] else [t35,t74,t97,t141,t156,t201,t226]) else (if i < 587 then [t35,t74,t97,t141,t197,t201,t226] else [t35,t38,t74,t97,t141,t201,t226])) else (if i < 590 then (if i < 589 then [t35,t74,t97,t141,t201,t226,t265] else [t35,t74,t88,t97,t141,t201]) else (if i < 591 then [t35,t74,t88,t97,t106,t141,t201] else [t35,t74,t88,t97,t141,t201,t226])))) else (if i < 600 then (if i < 596 then (if i < 594 then (if i < 593 then [t35,t60,t74,t97,t106,t141,t226] else [t35,t74,t97,t106,t141,t201,t211,t226]) else (if i < 595 then [t35,t74,t97,t106,t130,t141,t201,t226] else [t35,t46,t74,t97,t106,t141,t201])) else (if i < 598 then (if i < 597 then [t35,t74,t97,t141,t201,t226,t255] else [t35,t81,t97,t141,t201,t226]) else (if i < 599 then [t26,t35,t81,t97,t141,t201,t226] else [t35,t74,t81,t97,t141,t201,t226]))) else (if i < 604 then (if i < 602 then (if i < 601 then [t35,t74,t97,t141,t213,t226] else [t26,t35,t74,t97,t141,t213,t226]) else (if i < 603 then [t35,t74,t97,t141,t149,t201,t226] else [t4,t35,t74,t97,t141,t201,t226])) else (if i < 606 then (if i < 605 then [t35,t74,t97,t141,t201,t244] else [t26,t35,t74,t97,t141,t201,t244]) else (if i < 607 then [t35,t74,t97,t141,t201,t226,t244] else [t26,t35,t97,t141,t184,t201,t226]))))) else (if i < 624 then (if i < 616 then (if i < 612 then (if i < 610 then (if i < 609 then [t26,t35,t74,t97,t141,t201,t243] else [t26,t35,t60,t74,t97,t141,t226]) else (if i < 611 then [t26,t35,t46,t74,t97,t141,t201] else [t7,t35,t74,t97,t150,t201,t226])) else (if i < 614 then (if i < 613 then [t7,t74,t97,t141,t150,t201,t226] else [t35,t74,t141,t196,t201,t226,t268]) else (if i < 615 then [t35,t97,t141,t150,t184,t201,t226] else [t35,t74,t97,t141,t217,t224,t226]))) else (if i < 620 then (if i < 618 then (if i < 617 then [t18,t35,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t150,t201,t243]) else (if i < 619 then [t35,t74,t97,t141,t217,t226,t268] else [t27,t35,t74,t97,t141,t201,t226])) else (if i < 622 then (if i < 621 then [t35,t60,t74,t97,t141,t217,t226] else [t35,t74,t97,t130,t141,t217,t226]) else (if i < 623 then [t35,t74,t97,t141,t217,t226,t261] else [t19,t35,t74,t97,t141,t201,t226])))) else (if i < 632 then (if i < 628 then (if i < 626 then (if i < 625 then [t35,t74,t97,t141,t201,t218,t226] else [t35,t74,t97,t131,t141,t201,t226]) else (if i < 627 then [t35,t74,t97,t141,t201,t226,t258] else [t35,t74,t97,t124,t141,t201,t226])) else (if i < 630 then (if i < 629 then [t35,t60,t74,t97,t141,t150,t226] else [t35,t46,t74,t97,t141,t150,t201]) else (if i < 631 then [t35,t74,t97,t141,t179,t201,t226] else [t35,t74,t78,t97,t141,t201,t226]))) else (if i < 636 then (if i < 634 then (if i < 633 then [t35,t41,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t145,t201,t226]) else (if i < 635 then [t6,t35,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t201,t226,t230])) else (if i < 638 then (if i < 637 then [t3,t35,t74,t97,t141,t201,t226] else [t7,t35,t97,t141,t184,t201,t226]) else (if i < 639 then [t7,t35,t74,t97,t141,t201,t243] else [t7,t35,t74,t97,t114,t201,t226]))))))) else (if i < 704 then (if i < 672 then (if i < 656 then (if i < 648 then (if i < 644 then (if i < 642 then (if i < 641 then [t7,t35,t60,t74,t97,t141,t226] else [t7,t35,t46,t74,t97,t141,t201]) else (if i < 643 then [t11,t35,t74,t97,t141,t201,t246] else [t11,t74,t97,t141,t201,t226,t246])) else (if i < 646 then (if i < 645 then [t35,t97,t141,t184,t201,t226,t246] else [t35,t74,t97,t141,t201,t243,t246]) else (if i < 647 then [t35,t71,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t201,t246,t264]))) else (if i < 652 then (if i < 650 then (if i < 649 then [t31,t35,t74,t97,t141,t201,t226] else [t35,t60,t74,t97,t141,t226,t246]) else (if i < 651 then [t35,t74,t97,t123,t141,t201,t226] else [t35,t46,t74,t97,t141,t201,t246])) else (if i < 654 then (if i < 653 then [t20,t35,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t170,t201,t226]) else (if i < 655 then [t35,t79,t97,t141,t201,t226] else [t11,t35,t79,t97,t141,t201,t226])))) else (if i < 664 then (if i < 660 then (if i < 658 then (if i < 657 then [t35,t74,t79,t97,t141,t201,t226] else [t35,t74,t104,t141,t201,t226]) else (if i < 659 then [t11,t35,t74,t104,t141,t201,t226] else [t35,t74,t91,t97,t141,t201,t226])) else (if i < 662 then (if i < 661 then [t35,t74,t97,t141,t208,t226] else [t11,t35,t74,t97,t141,t208,t226]) else (if i < 663 then [t35,t74,t97,t141,t143,t201,t226] else [t11,t35,t97,t141,t184,t201,t226]))) else (if i < 668 then (if i < 666 then (if i < 665 then [t11,t35,t74,t97,t141,t201,t243] else [t11,t35,t74,t87,t97,t141,t201]) else (if i < 667 then [t11,t35,t60,t74,t97,t141,t226] else [t11,t35,t46,t74,t97,t141,t201])) else (if i < 670 then (if i < 669 then [t35,t74,t74,t97,t141,t201,t243] else [t35,t60,t74,t74,t97,t141,t226]) else (if i < 671 then [t35,t46,t74,t74,t97,t141,t201] else [t35,t97,t141,t184,t186,t201,t226]))))) else (if i < 688 then (if i < 680 then (if i < 676 then (if i < 674 then (if i < 673 then [t30,t35,t97,t141,t184,t201,t226] else [t35,t97,t141,t141,t184,t201,t226]) else (if i < 675 then [t35,t60,t97,t141,t184,t226] else [t35,t60,t97,t141,t184,t201,t226])) else (if i < 678 then (if i < 677 then [t35,t97,t141,t184,t187,t201,t226] else [t35,t97,t132,t141,t184,t201,t226]) else (if i < 679 then [t35,t97,t141,t184,t201,t211,t226] else [t35,t97,t130,t141,t184,t201,t226]))) else (if i < 684 then (if i < 682 then (if i < 681 then [t35,t97,t141,t184,t201,t226,t251] else [t35,t97,t122,t141,t184,t201,t226]) else (if i < 683 then [t35,t97,t141,t184,t184,t201,t226] else [t35,t97,t141,t184,t201,t226,t257])) else (if i < 686 then (if i < 685 then [t35,t97,t141,t180,t184,t201] else [t35,t97,t141,t180,t184,t201,t226]) else (if i < 687 then [t35,t97,t141,t184,t201,t226,t226] else [t35,t46,t97,t141,t184,t201])))) else (if i < 696 then (if i < 692 then (if i < 690 then (if i < 689 then [t35,t46,t97,t141,t184,t201,t226] else [t35,t74,t97,t141,t186,t201,t226]) else (if i < 691 then [t30,t35,t74,t97,t141,t201,t226] else [t35,t97,t141,t177,t184,t201,t226])) else (if i < 694 then (if i < 693 then [t15,t35,t97,t141,t184,t201,t226] else [t35,t97,t141,t184,t201,t226,t270]) else (if i < 695 then [t1,t35,t97,t141,t184,t201,t226] else [t35,t97,t141,t184,t201,t243]))) else (if i < 700 then (if i < 698 then (if i < 697 then [t35,t74,t97,t141,t184,t201,t243] else [t35,t97,t141,t184,t201,t226,t243]) else (if i < 699 then [t35,t70,t97,t141,t184,t201,t226] else [t35,t60,t74,t97,t141,t184,t226])) else (if i < 702 then (if i < 701 then [t35,t74,t97,t141,t187,t201,t226] else [t35,t74,t97,t132,t141,t201,t226]) else (if i < 703 then [t35,t74,t97,t141,t201,t226,t257] else [t35,t74,t97,t141,t180,t201])))))) else (if i < 736 then (if i < 720 then (if i < 712 then (if i < 708 then (if i < 706 then (if i < 705 then [t35,t74,t97,t141,t180,t184,t201] else [t35,t74,t97,t141,t180,t201,t226]) else (if i < 707 then [t35,t46,t74,t97,t141,t184,t201] else [t10,t35,t74,t97,t141,t201,t226])) else (if i < 710 then (if i < 709 then [t15,t35,t74,t97,t177,t201,t226] else [t15,t35,t97,t141,t177,t201,t226]) else (if i < 711 then [t35,t97,t141,t177,t201,t224,t226] else [t35,t74,t97,t141,t177,t201,t243]))) else (if i < 716 then (if i < 714 then (if i < 713 then [t35,t60,t74,t97,t141,t224,t226] else [t35,t74,t97,t141,t211,t224,t226]) else (if i < 715 then [t35,t50,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t201,t225,t226])) else (if i < 718 then (if i < 717 then [t35,t74,t97,t135,t201,t226] else [t35,t74,t97,t135,t201,t224,t226]) else (if i < 719 then [t35,t74,t97,t135,t141,t201,t226] else [t35,t74,t97,t141,t201,t226,t256])))) else (if i < 728 then (if i < 724 then (if i < 722 then (if i < 721 then [t35,t74,t97,t141,t171,t201,t226] else [t35,t60,t74,t97,t141,t177,t226]) else (if i < 723 then [t35,t46,t74,t97,t141,t177,t201] else [t35,t74,t97,t141,t192,t201,t226])) else (if i < 726 then (if i < 725 then [t35,t74,t107,t141,t201,t226] else [t15,t35,t74,t107,t141,t201,t226]) else (if i < 727 then [t35,t36,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t210,t226]))) else (if i < 732 then (if i < 730 then (if i < 729 then [t15,t35,t74,t97,t141,t210,t226] else [t35,t74,t97,t141,t167,t201,t226]) else (if i < 731 then [t35,t74,t97,t141,t201,t232] else [t15,t35,t74,t97,t141,t201,t232])) else (if i < 734 then (if i < 733 then [t35,t74,t97,t141,t201,t226,t232] else [t5,t35,t74,t97,t141,t201,t226]) else (if i < 735 then [t15,t35,t74,t97,t141,t201,t243] else [t15,t35,t74,t97,t114,t201,t226]))))) else (if i < 752 then (if i < 744 then (if i < 740 then (if i < 738 then (if i < 737 then [t15,t35,t74,t97,t130,t201,t226] else [t15,t35,t60,t74,t97,t141,t226]) else (if i < 739 then [t15,t35,t46,t74,t97,t141,t201] else [t35,t74,t97,t141,t201,t243,t248])) else (if i < 742 then (if i < 741 then [t13,t35,t74,t97,t141,t201,t243] else [t35,t74,t97,t141,t201,t243,t243]) else (if i < 743 then [t35,t74,t97,t141,t141,t201,t243] else [t35,t60,t74,t97,t141,t243]))) else (if i < 748 then (if i < 746 then (if i < 745 then [t35,t60,t74,t97,t141,t201,t243] else [t35,t74,t97,t141,t201,t211,t243]) else (if i < 747 then [t35,t74,t97,t130,t141,t201,t243] else [t35,t74,t97,t141,t201,t243,t256])) else (if i < 750 then (if i < 749 then [t35,t74,t97,t125,t141,t201,t243] else [t35,t42,t74,t97,t141,t201]) else (if i < 751 then [t35,t42,t74,t97,t141,t201,t243] else [t13,t35,t74,t97,t141,t201,t226])))) else (if i < 760 then (if i < 756 then (if i < 754 then (if i < 753 then [t35,t70,t74,t97,t141,t201,t243] else [t35,t70,t97,t141,t201,t226,t243]) else (if i < 755 then [t35,t60,t74,t97,t141,t226,t243] else [t35,t74,t97,t141,t201,t243,t251])) else (if i < 758 then (if i < 757 then [t35,t74,t97,t122,t141,t201,t243] else [t35,t74,t97,t125,t141,t201,t226]) else (if i < 759 then [t35,t46,t74,t97,t141,t201,t243] else [t35,t42,t74,t97,t141,t201,t226]))) else (if i < 764 then (if i < 762 then (if i < 761 then [t35,t74,t80,t97,t141,t201,t226] else [t35,t74,t97,t141,t188,t201,t226]) else (if i < 763 then [t35,t74,t97,t141,t175,t201,t226] else [t35,t60,t70,t74,t97,t141,t226])) else (if i < 766 then (if i < 765 then [t35,t46,t70,t74,t97,t141,t201] else [t35,t60,t74,t97,t141,t141,t226]) else (if i < 767 then [t35,t46,t74,t97,t141,t141,t201] else [t35,t60,t64,t74,t97,t141,t226])))))))) else (if i < 896 then (if i < 832 then (if i < 800 then (if i < 784 then (if i < 776 then (if i < 772 then (if i < 770 then (if i < 769 then [t21,t35,t60,t74,t97,t141,t226] else [t35,t60,t60,t74,t97,t141,t226]) else (if i < 771 then [t35,t60,t74,t85,t97,t141,t226] else [t35,t52,t60,t74,t97,t141,t226])) else (if i < 774 then (if i < 773 then [t35,t60,t74,t97,t141,t154,t226] else [t16,t35,t60,t74,t97,t141,t226]) else (if i < 775 then [t35,t60,t74,t97,t141,t226,t238] else [t35,t56,t60,t74,t97,t141,t226]))) else (if i < 780 then (if i < 778 then (if i < 777 then [t35,t60,t74,t97,t114,t226] else [t35,t60,t74,t97,t114,t141,t226]) else (if i < 779 then [t35,t60,t74,t97,t141,t226,t251] else [t35,t60,t74,t97,t122,t141,t226])) else (if i < 782 then (if i < 781 then [t35,t60,t74,t97,t141,t226,t226] else [t35,t46,t60,t74,t97,t141]) else (if i < 783 then [t35,t46,t60,t74,t97,t141,t226] else [t35,t64,t74,t97,t141,t201,t226])))) else (if i < 792 then (if i < 788 then (if i < 786 then (if i < 785 then [t21,t35,t74,t97,t141,t201,t226] else [t35,t74,t85,t97,t141,t201,t226]) else (if i < 787 then [t35,t52,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t154,t201,t226])) else (if i < 790 then (if i < 789 then [t16,t35,t74,t97,t141,t201,t226] else [t35,t60,t74,t97,t141,t226,t270]) else (if i < 791 then [t1,t35,t60,t74,t97,t141,t226] else [t35,t74,t97,t141,t201,t226,t238]))) else (if i < 796 then (if i < 794 then (if i < 793 then [t35,t56,t74,t97,t141,t201,t226] else [t35,t60,t74,t97,t141,t211,t226]) else (if i < 795 then [t35,t60,t74,t97,t130,t141,t226] else [t35,t60,t74,t97,t141,t226,t261])) else (if i < 798 then (if i < 797 then [t35,t60,t74,t97,t141,t198,t226] else [t35,t46,t60,t74,t97,t141,t201]) else (if i < 799 then [t25,t35,t74,t97,t141,t201,t226] else [t35,t68,t74,t97,t141,t201,t226]))))) else (if i < 816 then (if i < 808 then (if i < 804 then (if i < 802 then (if i < 801 then [t35,t74,t97,t130,t211,t226] else [t35,t74,t97,t130,t141,t211,t226]) else (if i < 803 then [t35,t58,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t201,t226,t262])) else (if i < 806 then (if i < 805 then [t35,t74,t97,t141,t199,t201,t226] else [t35,t46,t74,t97,t141,t201,t211]) else (if i < 807 then [t35,t74,t141,t194,t201,t226] else [t35,t74,t97,t141,t148,t201,t226]))) else (if i < 812 then (if i < 810 then (if i < 809 then [t35,t74,t130,t141,t194,t201,t226] else [t35,t97,t141,t176,t201,t226]) else (if i < 811 then [t35,t74,t97,t141,t176,t201,t226] else [t35,t97,t130,t141,t176,t201,t226])) else (if i < 814 then (if i < 813 then [t35,t74,t97,t116,t141,t201,t226] else [t35,t74,t97,t141,t201,t249]) else (if i < 815 then [t35,t74,t97,t130,t141,t201,t249] else [t35,t74,t97,t141,t201,t226,t249])))) else (if i < 824 then (if i < 820 then (if i < 818 then (if i < 817 then [t35,t74,t97,t121,t141,t201,t226] else [t35,t46,t74,t97,t130,t141,t201]) else (if i < 819 then [t12,t35,t74,t97,t141,t201,t226] else [t35,t73,t74,t97,t141,t201,t226])) else (if i < 822 then (if i < 821 then [t35,t74,t97,t122,t141,t201,t251] else [t35,t74,t97,t122,t201,t226,t251]) else (if i < 823 then [t35,t74,t97,t141,t201,t251,t261] else [t35,t74,t97,t133,t141,t201,t226]))) else (if i < 828 then (if i < 826 then (if i < 825 then [t35,t46,t74,t97,t141,t201,t251] else [t22,t35,t74,t97,t141,t201,t226]) else (if i < 827 then [t35,t74,t97,t129,t141,t201,t226] else [t35,t74,t97,t141,t173,t201,t226])) else (if i < 830 then (if i < 829 then [t35,t65,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t200,t201,t226]) else (if i < 831 then [t35,t46,t74,t97,t122,t141,t201] else [t35,t46,t49,t74,t97,t141,t201])))))) else (if i < 864 then (if i < 848 then (if i < 840 then (if i < 836 then (if i < 834 then (if i < 833 then [t28,t35,t46,t74,t97,t141,t201] else [t35,t46,t46,t74,t97,t141,t201]) else (if i < 835 then [t35,t74,t84,t97,t141,t201] else [t35,t46,t74,t84,t97,t141,t201])) else (if i < 838 then (if i < 837 then [t24,t35,t46,t74,t97,t141,t201] else [t35,t46,t74,t97,t141,t152,t201]) else (if i < 839 then [t35,t39,t46,t74,t97,t141,t201] else [t35,t49,t74,t97,t141,t201,t226]))) else (if i < 844 then (if i < 842 then (if i < 841 then [t28,t35,t74,t97,t141,t201,t226] else [t35,t74,t84,t97,t141,t201,t226]) else (if i < 843 then [t24,t35,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t152,t201,t226])) else (if i < 846 then (if i < 845 then [t35,t39,t74,t97,t141,t201,t226] else [t35,t46,t74,t97,t141,t201,t270]) else (if i < 847 then [t1,t35,t46,t74,t97,t141,t201] else [t35,t74,t97,t141,t201,t226])))) else (if i < 856 then (if i < 852 then (if i < 850 then (if i < 849 then [t35,t35,t74,t97,t141,t201,t226] else [t35,t74,t141,t159,t201,t226]) else (if i < 851 then [t35,t74,t97,t141,t159,t201,t226] else [t35,t74,t83,t97,t141,t201,t226])) else (if i < 854 then (if i < 853 then [t9,t35,t74,t97,t141,t201,t226] else [t35,t74,t97,t106,t141,t201,t226]) else (if i < 855 then [t26,t35,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t150,t201,t226]))) else (if i < 860 then (if i < 858 then (if i < 857 then [t7,t35,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t201,t226,t246]) else (if i < 859 then [t11,t35,t74,t97,t141,t201,t226] else [t35,t74,t74,t97,t141,t201,t226])) else (if i < 862 then (if i < 861 then [t35,t97,t141,t184,t201,t226] else [t35,t74,t97,t141,t184,t201,t226]) else (if i < 863 then [t35,t74,t97,t141,t177,t201,t226] else [t15,t35,t74,t97,t141,t201,t226]))))) else (if i < 880 then (if i < 872 then (if i < 868 then (if i < 866 then (if i < 865 then [t35,t74,t97,t141,t201,t243] else [t35,t74,t97,t141,t201,t226,t243]) else (if i < 867 then [t35,t70,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t141,t201,t226])) else (if i < 870 then (if i < 869 then [t35,t60,t74,t97,t141,t226] else [t35,t60,t74,t97,t141,t201,t226]) else (if i < 871 then [t35,t74,t97,t141,t201,t211,t226] else [t35,t74,t97,t130,t141,t201,t226]))) else (if i < 876 then (if i < 874 then (if i < 873 then [t35,t74,t97,t141,t201,t226,t251] else [t35,t74,t97,t122,t141,t201,t226]) else (if i < 875 then [t35,t74,t97,t141,t201,t226,t226] else [t35,t46,t74,t97,t141,t201])) else (if i < 878 then (if i < 877 then [t35,t46,t74,t97,t141,t201,t226] else [t35,t74,t97,t141,t201,t226]) else []))) else []))) else [])))

def sixE (i : Nat) : Nat :=
  (0x05c08090ab2409103408154f725c901b048020922449304c24120ad244901b0080009324092034000909524c94120080009724496090001549525093120080009724096120081549625091020001549625091020000349424091034000909524094020000909524c94020000909324094034240009424c95020000909324891120000209624097020240009424c9509000034952509304c001209724490020000909324091020241b09724890090000209224493020240009324092034081549725890020001209724490 >>> (60 * i)) &&& 0xfffffffffffffff

def segE (i : Nat) : Nat :=
  (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x7000101 else 0x3000101) else (if i < 3 then 0x2500000001000100030000020503 else 0x3000101)) else (if i < 6 then (if i < 5 then 0x7000101 else 0x7000101) else (if i < 7 then 0x7000101 else 0x101))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x70000000700010101000305 else 0xb000200070007000500000007000300060302000807) else (if i < 11 then 0x100010003000100000402 else 0x100010003000100000402)) else (if i < 14 then (if i < 13 then 0x1000101 else 0x700050005000b000500010000000505) else (if i < 15 then 0x5000101 else 0x1000101)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x3000101 else 0x3000101) else (if i < 19 then 0x3000101 else 0x101)) else (if i < 22 then (if i < 21 then 0x1000101 else 0x1000000000003000300000302000505) else (if i < 23 then 0x1000101 else 0x10010000300000025000100130001000100000105010905))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x1000101 else 0x1000101) else (if i < 27 then 0x100010003000100000402 else 0x100010003000100000402)) else (if i < 30 then (if i < 29 then 0x3000101 else 0x1002000000003000300000302000505) else (if i < 31 then 0x100010003000100000402 else 0x100010003000100000402))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0x1000101 else 0x1000101) else (if i < 35 then 0x10010000300000025000100130001000100000105010905 else 0x1000101)) else (if i < 38 then (if i < 37 then 0x1000101 else 0x20000300030000000001000201000309) else (if i < 39 then 0x101 else 0x13001000250001000100010003000102010000000805))) else (if i < 44 then (if i < 42 then (if i < 41 then 0x100010003000100000402 else 0x1000101) else (if i < 43 then 0x1000101 else 0x1000101)) else (if i < 46 then (if i < 45 then 0x1000101 else 0x1000101) else (if i < 47 then 0x1000101 else 0x1f0005000f0200000303)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0xf000100000202 else 0xf000b00000202) else (if i < 51 then 0x3000101 else 0xf0005000f0200010000000101010001030b)) else (if i < 54 then (if i < 53 then 0x100010003000100000402 else 0x1000101) else (if i < 55 then 0x300007000700020100000305 else 0x7000700300100000101010100010309))) else (if i < 60 then (if i < 58 then (if i < 57 then 0x400007000700020100000305 else 0x7000700400100000101010100010309) else (if i < 59 then 0x700320030004000070007000b000700050007010302030703000a07 else 0x50005000b00070001030403)) else (if i < 62 then (if i < 61 then 0x50007000b000102000001020307 else 0x7000b000500050000000200000002000409) else (if i < 63 then 0xb000700050002000000020102000309 else 0xb001100070007000000000200000407)))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0x1002000000003000300000302000505 else 0x20000300030000000001000201000309) else (if i < 67 then 0x500007000700020100000305 else 0x40000b0050000700520007000700050007000601000000000200000102090c)) else (if i < 70 then (if i < 69 then 0x4000070007000000070007000f0300010703 else 0x700500007006000070007000701000702) else (if i < 71 then 0x62006000000000000205 else 0x7000b000500050000000000000002000000040b))) else (if i < 76 then (if i < 74 then (if i < 73 then 0x5000b0005000700050004000503 else 0x5000b0005000700050004000503) else (if i < 75 then 0x5000101 else 0x7000070005000700720080000b00070007070005060300010907)) else (if i < 78 then (if i < 77 then 0x700800007000f000f0019000700110007040100020607000907 else 0x5000101) else (if i < 79 then 0x5000101 else 0x700050005000b000500010000000505)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 0x101 else 0x101) else (if i < 83 then 0x3000100000202 else 0x1000101)) else (if i < 86 then (if i < 85 then 0x1000101 else 0x300030001000002000000010407) else (if i < 87 then 0x1000101 else 0x1000101))) else (if i < 92 then (if i < 90 then (if i < 89 then 0x101 else 0x101) else (if i < 91 then 0x3000101 else 0x101)) else (if i < 94 then (if i < 93 then 0x101 else 0x30001000f00010001040000000300000507) else (if i < 95 then 0x3000101 else 0x3000100000202))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 0x3000101 else 0x30010000100010013000100010001000000000304000907) else (if i < 99 then 0x10001000100010020000700010402000703 else 0x1000000010001000302000401020505)) else (if i < 102 then (if i < 101 then 0x3000100000202 else 0x1001000010001000302000401020505) else (if i < 103 then 0x300010001000100000001000405 else 0x300010001000100000001000405))) else (if i < 108 then (if i < 106 then (if i < 105 then 0x3000100000202 else 0x101) else (if i < 107 then 0x1000101 else 0x101)) else (if i < 110 then (if i < 109 then 0x3000101 else 0x3000100000202) else (if i < 111 then 0x7001500110007000700070000000401000606 else 0x7000101)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 0x7000101 else 0x3000101) else (if i < 115 then 0x3000101 else 0x3000101)) else (if i < 118 then (if i < 117 then 0x101 else 0x101) else (if i < 119 then 0x50007000700300005000b0005000500040007000003070808 else 0x700050005000500000001000405))) else (if i < 124 then (if i < 122 then (if i < 121 then 0x500300005000b000700050002000403050105000609 else 0x3000101) else (if i < 123 then 0x1000101 else 0x101)) else (if i < 126 then (if i < 125 then 0x101 else 0x101) else (if i < 127 then 0x101 else 0x1000101))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 0x1000101 else 0x3000101) else (if i < 131 then 0x101 else 0x1000101)) else (if i < 134 then (if i < 133 then 0x1000101 else 0x101) else (if i < 135 then 0x101 else 0x101))) else (if i < 140 then (if i < 138 then (if i < 137 then 0x101 else 0x1000101) else (if i < 139 then 0x7000101 else 0x5000101)) else (if i < 142 then (if i < 141 then 0x1000101 else 0x7000101) else (if i < 143 then 0x3000101 else 0x101)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 0x3000101 else 0x3000101) else (if i < 147 then 0x101 else 0x101)) else (if i < 150 then (if i < 149 then 0x101 else 0x101) else (if i < 151 then 0x101 else 0x1000101))) else (if i < 156 then (if i < 154 then (if i < 153 then 0x5004000000202 else 0x1000101) else (if i < 155 then 0x5004000000202 else 0x1000101)) else (if i < 158 then (if i < 157 then 0x3000101 else 0x101) else (if i < 159 then 0x101 else 0x1005000000202))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 0x1000101 else 0x1000101) else (if i < 163 then 0x1000101 else 0x3000101)) else (if i < 166 then (if i < 165 then 0x1000101 else 0x1000101) else (if i < 167 then 0x1000101 else 0x300030001000001000000010407))) else (if i < 172 then (if i < 170 then (if i < 169 then 0x300030001000002000000010407 else 0x1000101) else (if i < 171 then 0x1000101 else 0x1000101)) else (if i < 174 then (if i < 173 then 0x30001000100010000000403 else 0x101) else (if i < 175 then 0x101 else 0x101)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 0x101 else 0x90000000f000100010001000000000001000607) else (if i < 179 then 0x30000006000030003000300030003000300130000010a03 else 0x30003000f000300030003000601)) else (if i < 182 then (if i < 181 then 0x3000f000f000f0019000001030000020507 else 0x8200000086000f00030003007000030003000300010003010002030b06) else (if i < 183 then 0x3000101 else 0x3002000010001000100020100000100000508))) else (if i < 188 then (if i < 186 then (if i < 185 then 0x1000300030001000002000000010407 else 0x1000101) else (if i < 187 then 0x1000101 else 0x7000100200000010201000100000001030b)) else (if i < 190 then (if i < 189 then 0x3000100000202 else 0x300600003000202010001000307) else (if i < 191 then 0x70001000500010001000103000602 else 0x3000101)))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 0x3000100000202 else 0x3000100000202) else (if i < 195 then 0x3000101 else 0x3000101)) else (if i < 198 then (if i < 197 then 0x3000101 else 0x3000101) else (if i < 199 then 0x3000101 else 0x3000101))) else (if i < 204 then (if i < 202 then (if i < 201 then 0x3000101 else 0x1000101) else (if i < 203 then 0x300030001000002000000010407 else 0x3000101)) else (if i < 206 then (if i < 205 then 0x1000101 else 0x1000101) else (if i < 207 then 0x3000101 else 0x3000101)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 0x3000100000202 else 0x3000100000202) else (if i < 211 then 0x3000100000202 else 0x3000101)) else (if i < 214 then (if i < 213 then 0x3000101 else 0x1000101) else (if i < 215 then 0x3000100000202 else 0x3000100000202))) else (if i < 220 then (if i < 218 then (if i < 217 then 0x1000101 else 0x1000101) else (if i < 219 then 0x1009000000202 else 0xe000b000e400c00000000d001300f00000000100010001001f00010025002300a0000300010003001f00010021001f000100d00003000109170a1b09130919071301180313000b15131c12)) else (if i < 222 then (if i < 221 then 0x1100001001f00010100000100130001000000010003010400010001050a0005000101000001010003010e0e else 0x13001200001001300230003002100010013001f000000130013000100130002000505000301000200040500030103000f12) else (if i < 223 then 0x10140001f00030013000101000001000101500001000000050004010200010000000b0d else 0x1900130019401700010000d001301a00010000100010001001f0001002500230160000300010003001f00010021001f000101800003000109170a1b09130919071301180313000b15131c12))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 0x1000101500010001f00010001001000010013011001540003000100010001000100020c0002010007011109 else 0x10000300030001000d00010001000000020400000101000001020000070f) else (if i < 227 then 0x1016000000202 else 0x300030013000301200130000101b000030200060200050306000000040200090e)) else (if i < 230 then (if i < 229 then 0x100c001c0017000000000000503 else 0x1018000130001002500d0000100010001000101d000030501030002030000020c09) else (if i < 231 then 0xe00001019000000000000305 else 0x100f000000202))) else (if i < 236 then (if i < 234 then (if i < 233 then 0x2500010001000300010000000100010001000308010008030a05 else 0x2500010001000300010010000100010001000308010008030a05) else (if i < 235 then 0x10001000100100001000100030000050703 else 0x1e000030010000100010013000100010001000000000304000907)) else (if i < 238 then (if i < 237 then 0x1000101 else 0x3000100000202) else (if i < 239 then 0x3000101 else 0x27002100070100010303)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 0x3002000070013000301b00003000300030100000500080100000300090b else 0x3000101) else (if i < 243 then 0x7000100000202 else 0x1000701f00001000100010001020000010207000903)) else (if i < 246 then (if i < 245 then 0x9005200030001000100070220000b0003000102240005021000010050000100200000000308010007020e00080a0c000306050003040b0003020100080f0100111f else 0x70007000900010003000500010007002000070001000a03000a03000000010b0a) else (if i < 247 then 0x50007020000200001000100010202023000010001000102340502010a020001030300010d0b else 0x1000101))) else (if i < 252 then (if i < 250 then (if i < 249 then 0x5000702400001000102300001060200060001000807 else 0x1022000000202) else (if i < 251 then 0x10001000101d0002500030009000100200300010202000100000001090b else 0x30001000d000100010300000200000001000000050b)) else (if i < 254 then (if i < 253 then 0x3000100000202 else 0x1f02500005000f000000000404) else (if i < 255 then 0x25000270005000f001f020402020200000507 else 0x3000101)))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 0x3000100000202 else 0x100a000000202) else (if i < 259 then 0x300010003000300b0020001010000020507 else 0x100e000000202)) else (if i < 262 then (if i < 261 then 0x100f000000202 else 0x1010000010001000302000401020505) else (if i < 263 then 0x1011000010001000302000401020505 else 0x30001000300030120020001010000020507))) else (if i < 268 then (if i < 266 then (if i < 265 then 0x30001000300030130020001010000020507 else 0x1000101) else (if i < 267 then 0x300030001000002000000010407 else 0x1000101)) else (if i < 270 then (if i < 269 then 0x1000101 else 0x1000101) else (if i < 271 then 0x1014000010001000302000401020505 else 0x1015000010001000302000401020505)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 0x3000100000202 else 0x3000100000202) else (if i < 275 then 0x3000100000202 else 0x1016000000202)) else (if i < 278 then (if i < 277 then 0x1019000000202 else 0x101a000000202) else (if i < 279 then 0x1000101 else 0xb0001000b0280000f000b02600003000f000b0270000b040800020701060c07))) else (if i < 284 then (if i < 282 then (if i < 281 then 0x110011000f0011001100270100000102010200010609 else 0xf000101) else (if i < 283 then 0xf000101 else 0x3000101)) else (if i < 286 then (if i < 285 then 0x1700050272002700050290000500050011000000050003000300030101000b09 else 0x262001100050005000500000000000101000508) else (if i < 287 then 0x28200050003000300110300010000000103000001050b else 0xf029000050005000500050000020504000606))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 0x1000300000202 else 0x3000100000202) else (if i < 291 then 0x3000100000202 else 0x3000100000202)) else (if i < 294 then (if i < 293 then 0x3000100000202 else 0x3000100000202) else (if i < 295 then 0x3000100000202 else 0x30001000500010001000100010100010703))) else (if i < 300 then (if i < 298 then (if i < 297 then 0x30001000500010001000100010100010703 else 0xd000101) else (if i < 299 then 0x302a20003000202010002000307 else 0x300030001002501e0000100010000000000000600010709)) else (if i < 302 then (if i < 301 then 0x300210001000401 else 0x3000100000202) else (if i < 303 then 0x3000100000202 else 0x1000101)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 0x2000010007000002b000010001000100010000000008010906 else 0x1000101) else (if i < 307 then 0x1000101 else 0x300010001000100000001000405)) else (if i < 310 then (if i < 309 then 0x300010001000100000001000405 else 0x1000101) else (if i < 311 then 0x1000300030001000002000000010407 else 0x1000101))) else (if i < 316 then (if i < 314 then (if i < 313 then 0x1000101 else 0x1000101) else (if i < 315 then 0x300010001000100000001000405 else 0x1f0000100010001000700010001000102b20000030903)) else (if i < 318 then (if i < 317 then 0x1000101 else 0x300030001000002000000010407) else (if i < 319 then 0x1000101 else 0x1000101)))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 0x1000101 else 0x300010001000100000001000405) else (if i < 323 then 0x1000101 else 0x1000101)) else (if i < 326 then (if i < 325 then 0x101 else 0x1000101) else (if i < 327 then 0x101 else 0x101))) else (if i < 332 then (if i < 330 then (if i < 329 then 0x101 else 0x101) else (if i < 331 then 0x1000101 else 0x5000101)) else (if i < 334 then (if i < 333 then 0x5000101 else 0x3000101) else (if i < 335 then 0x101 else 0x101)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 0x101 else 0x3000101) else (if i < 339 then 0x3000100000202 else 0x7000101)) else (if i < 342 then (if i < 341 then 0x7000101 else 0x7000101) else (if i < 343 then 0x3000101 else 0x101))) else (if i < 348 then (if i < 346 then (if i < 345 then 0x1000101 else 0x1000101) else (if i < 347 then 0x3000100000202 else 0x2c0000702d0000700070101010000010506)) else (if i < 350 then (if i < 349 then 0x7000702e0000702f000070005010005020100060707 else 0x2c00007000702e400070007000502c20007000b0300000406020007060b07) else (if i < 351 then 0x7030002f0000b02d000070007000502d200070007000700070007010d01000008000100000e0a else 0x23000101))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 0x5003000070005000b0100010104000103000001050b else 0x70007000703040007001b00110007060207020107000807) else (if i < 355 then 0x7000101 else 0x30000700070007000f000002010101010507)) else (if i < 358 then (if i < 357 then 0x3000100000202 else 0x1103240314033400070007000700070007001500070000050300020103000400020b0c) else (if i < 359 then 0x32400070005000700070344000b001100070326000700150007020800010601000d07 else 0x5000101))) else (if i < 364 then (if i < 362 then (if i < 361 then 0x344000700070007001500110201020500020200000102060b else 0x7000700150336000700110334000102020004020004010200000102070f) else (if i < 363 then 0x7000101 else 0x7000f00110007000700070000000400000606)) else (if i < 366 then (if i < 365 then 0x3000101 else 0x3000101) else (if i < 367 then 0x1000101 else 0x3000100000202)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 0x3000100000202 else 0x702c000110007001900070000000500000606) else (if i < 371 then 0x1000101 else 0x1000101)) else (if i < 374 then (if i < 373 then 0x350000700070007000b00110201020500020200000102060b else 0x7000101) else (if i < 375 then 0x7000101 else 0x7000101))) else (if i < 380 then (if i < 378 then (if i < 377 then 0x7000101 else 0x7000101) else (if i < 379 then 0x702e400110007001b00070000000500000606 else 0x1000101)) else (if i < 382 then (if i < 381 then 0x7000101 else 0x7000101) else (if i < 383 then 0x7000101 else 0x50007000703400005000b0005000500040007000003070808))))))) else (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 0x1000101 else 0x3000101) else (if i < 387 then 0x1000101 else 0x3000100000202)) else (if i < 390 then (if i < 389 then 0x3000100000202 else 0xb0000001100070344000700000000035000150007000503520007000701000706000f05) else (if i < 391 then 0x1000101 else 0x370000300030362000300030300000001000201000609))) else (if i < 396 then (if i < 394 then (if i < 393 then 0x372000300030000000001000101000309 else 0x70000000030003036200130003000300030800020903) else (if i < 395 then 0x100030013000300820000010000000104020001050b else 0x101)) else (if i < 398 then (if i < 397 then 0x101 else 0x70390000703800007000b0000000700070005038202010800020b05) else (if i < 399 then 0x70007000700110000000700190390000f0007000703a00100000202000002090d09 else 0x70011000f000700090007030100010301000707)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 0x11000700090001000f03a000030007001b00070007000005010300000000000005000b0d else 0x3000101) else (if i < 403 then 0x3000101 else 0x1000101)) else (if i < 406 then (if i < 405 then 0x1000100030200010303 else 0x300130003000302a2000001010000010507) else (if i < 407 then 0x3000100000202 else 0x101))) else (if i < 412 then (if i < 410 then (if i < 409 then 0x3000101 else 0x101) else (if i < 411 then 0x3000101 else 0x101)) else (if i < 414 then (if i < 413 then 0x101 else 0x101) else (if i < 415 then 0x101 else 0x3000100000202))))) else (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 0x3000101 else 0x5000101) else (if i < 419 then 0x5000101 else 0x3000101)) else (if i < 422 then (if i < 421 then 0x38000070007000703b0000700010100000605 else 0x3000101) else (if i < 423 then 0x3c002f00007000b03b000000007000503b20390000700070007010002000000010200000201000d0d else 0x3f00005000503d003e0000b00070005000500000702000001000100030201000003000911))) else (if i < 428 then (if i < 426 then (if i < 425 then 0x2920040001b04200440000500420290041004300007040000110030000b00070005000500050005000500050007000b0005001f0250000f003502000118170f0013040f04110d0f081b050f0616040f1d16 else 0x502f0000f000f000b00300011001b03c00007000503a000070007000409010103030600000606000e0d) else (if i < 427 then 0x5003000000007000503e00005000b000503e2000b045000070005000500050007000504010102040a0101001209 else 0x5046000000202)) else (if i < 430 then (if i < 429 then 0x45003f0000503f2000500070005000b0005000501000002000700020001000403000a0e else 0x5047004300001000303) else (if i < 431 then 0x5044000000202 else 0x5000b0005003000070005000b0005000500050023000700050502000000020c08)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 0x5000101 else 0x5000101) else (if i < 435 then 0x7000b000703d00005000500050000010000000002000709 else 0x70005000b0005000503e000050100010206030706)) else (if i < 438 then (if i < 437 then 0x50007000703f000050005000b0100000201000004010709 else 0x5040000000202) else (if i < 439 then 0x1b001100190011000f000700070420000700030000000001010200000000010000000911 else 0x5044000000202))) else (if i < 444 then (if i < 442 then (if i < 441 then 0x504500005000b000700050002000403050105000609 else 0x3000100000202) else (if i < 443 then 0x3000100000202 else 0x3000101)) else (if i < 446 then (if i < 445 then 0x3000100000202 else 0x3000100000202) else (if i < 447 then 0x1000101 else 0x101)))))) else (if i < 480 then (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 0x101 else 0x101) else (if i < 451 then 0x400005000d0050001200030009000b000500050010000700010001002000070003000100300001004400000000000305020100010c060001000515140402121704010a030f01060d040106090802001304011823 else 0x100000003000100010001000100010005010401000604040907)) else (if i < 454 then (if i < 453 then 0x800001007000a0009400100090006000100009060803020103000a09 else 0x10005000300010001000100070001000700050507020807) else (if i < 455 then 0x50001000f0001001100010007000100000003000100b0000100010104000103010001010800010001000d11 else 0x7000100c00001000300e0000500d0000300d40003000000010003030007010b0000080400000304000001010000010800050100000e1a))) else (if i < 460 then (if i < 458 then (if i < 457 then 0x300010009000f000000010000000100f00001010000030001000100060100020103000001010000010e0e else 0x500130000000300010130000000010001012400f00001000101100001012000010001000b060100060a010000020c00000100001211) else (if i < 459 then 0x5000000010000000f000f00030005000100050005000a010202010005000103000003020900010c12 else 0x7000100010003000000050001000100010001000100000001000200020902000d07)) else (if i < 462 then (if i < 461 then 0x3000100010000000100010001000b0001000100030103000705000001010b09 else 0x101600150000100010003000101640001000000050140000100010007000100010208010c0001030900030e000003110e) else (if i < 463 then 0x1000100050009000700010007000000030030000000070001010500000900070301000001010e0d else 0x1740180019000700170000000200001007202000805020105030201000202090d)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 0x101b00001000301a0000000010005000700010001000300000000000100000200000b0d else 0x1000500050007000b000500050003000100070003000501c400000005000500000a0a000202040d060e1209) else (if i < 467 then 0x701e0000100030007000700050000000b01d00001000000010007000501d20007000701f00007000700011503020802010011021709 else 0xb201a0008000300011020000030204000300300003021000070082001300300003000f00b00003120502010403020004050005000500050007080904030e0004090c070a0911000a09120704000603041429)) else (if i < 470 then (if i < 469 then 0x300000000300030001000f0000000700030007000300010003000300010100030802000009060001080201040e010f11 else 0x1000100000007000d00010005000100010003010100000103050102000100020a0d) else (if i < 471 then 0x30005000b000700010001000100050005000608010100070801000203000a0d else 0x900200009200400220000302300170004001040003090400070604000a0b))) else (if i < 476 then (if i < 474 then (if i < 473 then 0x30003000700050003000102010100010500040005060a else 0x70000000b0001024000030000000500050001000000050001000500070400010405000608000501050300010f0f) else (if i < 475 then 0x9026002400003000b00000005000100070005000502700001000b0252025000050005000100050108000f05040304040900020102020a030003060f060007030000141b else 0x30007000300030005000300030001000304080204040105000102000101090f)) else (if i < 478 then (if i < 477 then 0x100050003000100070001000000010000000100010001000100000100000805000d08 else 0x30001000d000100010500000502000004000000060b) else (if i < 479 then 0x280000d023000a000000234019000a200500050005009060000000300000b08 else 0xd000f0001000d000d000d000500010001000000030006010300010003090c))))) else (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 0x1002000000202 else 0x3000300b00000000f00030030000300030011000300010003000300030100040608000f06) else (if i < 483 then 0x1001000000202 else 0x1004000000202)) else (if i < 486 then (if i < 485 then 0x1005000000202 else 0x1002b002b402a000600060006002c00012029000070003000000030a08) else (if i < 487 then 0x3000101 else 0x2d0001000010000000303))) else (if i < 492 then (if i < 490 then (if i < 489 then 0x3001002e4001002f0001002e00100000703 else 0x5001000000202) else (if i < 491 then 0x1001000000202 else 0x103000010000301)) else (if i < 494 then (if i < 493 then 0x1003000001000301 else 0x1001000000202) else (if i < 495 then 0x3200010000103240310030300000000000507 else 0x80001000070001000303)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 0x334001000200350034000700330029000700002080603020105000909 else 0x360000103700000000303) else (if i < 499 then 0x50384001000010000020305 else 0x703900010001003c003a003b00100000703)) else (if i < 502 then (if i < 501 then 0x1001003d000000000000305 else 0x3d0000703f0001003e00004000300000506) else (if i < 503 then 0x3036002d00080003002a00410040000800080040403f002010a0603010600020c09 else 0x10000300800002010303))) else (if i < 508 then (if i < 506 then (if i < 505 then 0x1001000000202 else 0x5001000000202) else (if i < 507 then 0x42003300400043000100090004002b000900002040703020106000909 else 0x3000101)) else (if i < 510 then (if i < 509 then 0x44004540010001000010102000503 else 0x50010044000020000000305) else (if i < 511 then 0x10000504600002000303 else 0x48004900010047000100005046004a0000006000000010905))))))))) else (if i < 768 then (if i < 640 then (if i < 576 then (if i < 544 then (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 0x3001000000202 else 0x1001000000202) else (if i < 515 then 0x1001000000202 else 0x104b00010020000000002000307)) else (if i < 518 then (if i < 517 then 0x1004b000010000000303 else 0x1001000000202) else (if i < 519 then 0x4c00430043400100050035002c000a000a000a000060000000309000a08 else 0xd000101))) else (if i < 524 then (if i < 522 then (if i < 521 then 0x4d000100001000301 else 0x1001004f404e00500000004f00100000703) else (if i < 523 then 0x10007000500010001000301010106010100000100030101000000010711 else 0x5000100010003000100030001000100030001000109020200000c05)) else (if i < 526 then (if i < 525 then 0x1000101 else 0x510001000090000000303) else (if i < 527 then 0x12053605220003053205420100000703 else 0x1000100010001000000010001000300050007000100040602000b05)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 0x550000000000007000300090005000700010560000700070001000700030007000700070e090900060105010400090400120d else 0x10007051000030003000300030560000300030003000500010200010603000b0a) else (if i < 531 then 0xb001000000202 else 0x1001200000202)) else (if i < 534 then (if i < 533 then 0x7000100000003000000010001000500010001000100010006030000080401000403000c0c else 0x1001000000202) else (if i < 535 then 0x10000000100010005000100010000000100000003000100070001000a01060b01010700010000000f0d else 0x1001000000202))) else (if i < 540 then (if i < 538 then (if i < 537 then 0x1001000000202 else 0x572059605820001059200120100000703) else (if i < 539 then 0x1000101 else 0x500070001000000010001000100030001000105a40105000402010000020b09)) else (if i < 542 then (if i < 541 then 0x1000b0005000100070001000500030007000500050001000500050000000500090301020303020000100a else 0x1000500070001000300010001000100040000000200030100090a) else (if i < 543 then 0x300010003000d0001000100010001000100010000000100010b00030d03 else 0x1000101))))) else (if i < 560 then (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then 0x5b0000005c00000000303 else 0x5d205e605e200000001000305) else (if i < 547 then 0x61000090009000f001300090003060000c000030001000905f0000900090013000900000401000f0002030007020800110e else 0xf000f000f00170000000b000f001b01d0000f000f0620000f000f000f000101010300010f07)) else (if i < 550 then (if i < 549 then 0x1002000000202 else 0x1100001001d00010009000105f00017000100010001070000000000000803000b0a) else (if i < 551 then 0x6220001000305120013001106420680000106700003000106300674000102d0001100b0000100b000010660065000170001000300b0000300010626061200010003011e0000050c0305000c19160f00170c060813100d04110c0f001a010f001d150d2121 else 0x70000000f00b00011000700030001000100070011001100300013001100030013001110040304020500020a00070b02080002090000010605001217))) else (if i < 556 then (if i < 554 then (if i < 553 then 0x100010001000100010140000d00010001000f000300b000010108000b050305040208040d0b else 0x9000300010640000500010001000105000806010905) else (if i < 555 then 0x50001000000010001000100010690000706500001000300010201000300010900020c0000000d0d else 0x500c0000306a4000100130001000306b0000006a00003060000030110000100030c0907010900000c040000030400000101000001080505010100111a)) else (if i < 558 then (if i < 557 then 0x6c4000700070001000100050001000100050201030501000000060200080100040911 else 0x500050000000501d20007000100010005000b00050005010009000100070403000400000c0d) else (if i < 559 then 0x300000007000106d200010001000000050001090200010105030101020300010200010502000a13 else 0x100010003000001400005000100070001000d00010001000102060703030000050a000d0a)))) else (if i < 568 then (if i < 564 then (if i < 562 then (if i < 561 then 0x670000100400100020303 else 0x1005000000202) else (if i < 563 then 0x106f00001000506e000000001000706e400030001080700090807000608030602000b0d else 0x70000030003072007340522001100c0000300090005000f000300c000030710000f05b00003074005d207300803020300030003000900030801020502090e0300030803110b080312070803150a08071007081627)) else (if i < 566 then (if i < 565 then 0x76007500003000300050754000f000300c0000300c000030003000300030100020100000d0000010100000e0f else 0x10001000100c2000100030003000100010000000f00010300040200000006000a040600040c0e) else (if i < 567 then 0x1000107800001000305320794000d000102e000050009000100010001000f0001077000d007a2000107b005e200d00003000b0a0f11010503120b00100203000304030003110d00090e0a0009060805131207051825 else 0x3000f07d0075000d000030001000307c000030003000300d000030001000500030001000803030004020000010b001101120e))) else (if i < 572 then (if i < 570 then (if i < 569 then 0xf000f0005000f0000000500d4000300050005000500030005000100050204050707020501010009080002010502000f12 else 0x7f007e000070001000000000800000100010001000300010001000100010005000106000006000007040300110a) else (if i < 571 then 0x54205c000300810083202f0082000e00005000300030009000f0003082400050003000300070003001100030003000005000000000001140a12000f0310000f0908070f0111010f0313040f0016000f1722 else 0x5000307d407600007000300e000e00003000300e0000307d000030003000300030101030001020004021109)) else (if i < 574 then (if i < 573 then 0xb0003000100e0000f00030003000300000202000000060008000201000307000911 else 0x850084000070001085400000000000100010001000300010001000100010005000106000006000007030300110a) else (if i < 575 then 0x30020077407000810000007700100000703 else 0x780000700030710000f0784000300030003003000030003000300030108000103010000040000020001000e0f)))))) else (if i < 608 then (if i < 592 then (if i < 584 then (if i < 580 then (if i < 578 then (if i < 577 then 0x30040004008600820073007900103000703 else 0x300500050087007b0074007b40103000703) else (if i < 579 then 0x8a00001001308b0000308900025088000f0095000f0000108f00021001f00030940094408c0001f00010003090008c40930001f001300010910000100f008e00023000d00f00001000108d00920000100010001001f00002729262410092101081b1a0108061900201b040f080214100c0123010c2b1f else 0x10003000109700001096000010025001300f00001000100010001030a0c070300050b000e09)) else (if i < 582 then (if i < 581 then 0x99000030001098000010003015000010001000100000101000008020002010b09 else 0x9a000200020000109000102000503) else (if i < 583 then 0xf0001000309c00001000309b00007000309b4000300c00000000100c200010003000300040e000001090000020200000405001210 else 0x1f00030001000509d40001000f030001020300050707))) else (if i < 588 then (if i < 586 then (if i < 585 then 0x300130001000f09e00003000300030003003000070610000309100001061200030003065000030003000d0e00110d020b0501150a else 0x9f000030003092000010003000700030003050600000500010202000003000003090f) else (if i < 587 then 0x50001000f000f000f00010001000f0000000f000f00030000000f000f0a000000000f000103000f0b0300051307 else 0x100050001000100030001000000050001000100090001050001040200000a0b)) else (if i < 590 then (if i < 589 then 0x100030001000000010001000000070001000100000101000602010003010b09 else 0xa4009a0000900050a50000104d0000504d20005010000010a2000070a300001010000010a64000101000003000b0a100a120a6000010a7400030a701c1002010006020104060001000600191108000a0d0a0216130c1703090a1903130a1c100901150e0d1e29) else (if i < 591 then 0x301000001000101000100000900010a800930000100130001000100250400040d0200000d0c010000010f0d else 0x1000300000005000101000000000100010aa00001000100010aa40150000100070a900152000d000300010001060300020a00000102000105020600180f)))) else (if i < 600 then (if i < 596 then (if i < 594 then (if i < 593 then 0x94000400a7000010000000000010000010409 else 0x50ab00001000f001f00010500000005020000020609) else (if i < 595 then 0x90ab000050027001f000f00010ac0000303010000000706040000000100020001020911 else 0xad00001095000500100000403)) else (if i < 598 then (if i < 597 then 0xae408800001000100000001000700030ae0000100050003050000040501060008020004010b0f else 0xb0004e20b20001f0b100af004e00890001301100960001f0b140025000109620001001f001f0001000300210003000100010001000100230001000100090003000d051b02000b00001e0817011c121704140f17031a1017031b18170a1f0317211e) else (if i < 599 then 0x1300010b4000010b300001000300010b34000108a0000101100001001f011000010001000e010d0001010000010c000001120e else 0xb5000000000001f00230007001300130003000500010110000300130023001300010000000100210009001308b00013000100130b60001300010e0103120a060110000c030b1000011d0f))) else (if i < 604 then (if i < 602 then (if i < 601 then 0x2300250ba0001f000d0bb004f200030009001f001f001f04f00021000100010b700013000300010b8000010b94012001200003160201000116060001000515140402121704010a030f01060d040106090802001304011a23 else 0x1f00130120000300010bd00120000100010bc008c0000100010b3000010000000100010002060100060a010000020c00000100001211) else (if i < 603 then 0x30001012400000005000500010005000500010005000500010001000b000500050007000500030c00110601020e05030e000904140d else 0xbf000000be00001000000000c0000010001000100030001000100070001000500010600000600000d070300110a)) else (if i < 606 then (if i < 605 then 0xb6005020c30001f0c200c10050008d0001301300970001f0c240025000109720001001f001f0001000300210003000100010001000100230001000100090003000d051b02000b00001e0817011c121704140f17031a1017031b18170a1f0317211e else 0x1f001301300003000101300130000100010bd408e0000100010b4000010bd000010001000b060100060a010000020c00000100001211) else (if i < 607 then 0x8f00001000101300001000d000100000003000d00010004000300060001010000050104000500060b12 else 0xb700c10002000010000090000200b74002000020100050905))))) else (if i < 624 then (if i < 616 then (if i < 612 then (if i < 610 then (if i < 609 then 0xb50000300030b6000030b8000030003000700030003091000030001001300300b84000300030003020e0205000e03110000010200140d else 0xc200c40000100400b9000400b10094000060100030905) else (if i < 611 then 0x9500b2000500bb400500bb0000100050200050705 else 0x101)) else (if i < 614 then (if i < 613 then 0x101 else 0x25000170003000b000f000b000500090c50000b000b01000108000a01040002010107000001000300000000000b17) else (if i < 615 then 0x5002000000202 else 0x27000f00110011000300d0000f0009001100010011000f0c6000110011001100050200060106000005011109))) else (if i < 620 then (if i < 618 then (if i < 617 then 0xd4000701d2000f00030c7000010c900001000f0c80000f00050001001b00000003000f000f000f01000b030009000c0007040e00010604001511 else 0x30622000f000f00070030000f0011002b000f0003000f00000000000805010000020002000001000202020008000102000c1a) else (if i < 619 then 0xb002b000100090017012000010005000100010000000100030001000102050000060400000100000f0b else 0x11000100010003000000050001000100010001000101240001000200020902000d07)) else (if i < 622 then (if i < 621 then 0x1004000000202 else 0x50c520011000300050cb00027000500090ca0001700050cc00005001100050cd0000501040a0c001102010900130a) else (if i < 623 then 0x50160000100010003000100030001000200030100000100000001070e else 0x300010003000100010003000100070005040703000405080907)))) else (if i < 632 then (if i < 628 then (if i < 626 then (if i < 625 then 0x1000500000001000f000f0001000500050000000100050cd00b0000000b0000050500040805040002040d11 else 0x5000700070005000b0001000500010001025200030009000000010005000b00030005040a00060d020e00010200120b) else (if i < 627 then 0x30001000500000001000700010001000100010009000003010002020001020001000b0f else 0x100010007000300050164000100010000000100010403000a090000000100000b0b)) else (if i < 630 then (if i < 629 then 0x5004000000202 else 0x5005000000202) else (if i < 631 then 0x10005000300010001000100070001000700050507020807 else 0x100000003000700010007000500010003000000070003000000070005000700090ce002010709000d041207))) else (if i < 636 then (if i < 634 then (if i < 633 then 0x3000500010000000100030001000100070101000407000002000000080d else 0x5000000070001000b000500010003000500070005000500050000020c0500000b0004010001010d0e) else (if i < 635 then 0xd000cf00001000000000d1000010001000100030001000100070001000500010600000600000d070300110a else 0x100000000000100030001001b0001000100010108000100010002020b09)) else (if i < 638 then (if i < 637 then 0xd400d300d20000100000000000000010001000100030001000100070001000500010600000600000d070300110a else 0x1002000000202) else (if i < 639 then 0x300030030000300030003000300010ce0000300070a0700030005040606040b0a else 0x1004400000202))))))) else (if i < 704 then (if i < 672 then (if i < 656 then (if i < 648 then (if i < 644 then (if i < 642 then (if i < 641 then 0x1004000000202 else 0x1005000000202) else (if i < 643 then 0x10d600d5000010001001300030005000100010001000101000700090100000b0a else 0xd0d7200000202)) else (if i < 646 then (if i < 645 then 0x1002000000202 else 0x300010003000000e00d80000300030003000f0003000300300003000303020500030f05) else (if i < 647 then 0x5000300070000000300e0000100000001000300010003000b0003090000010400000803020e0a else 0x13000010001000309800001000100000002000400000100010100070d))) else (if i < 652 then (if i < 650 then (if i < 649 then 0x1000101300003000100010da00001000300250da4001300000001015000010d900001000000050000099000010001100101000c1005000006180a else 0x1004000000202) else (if i < 651 then 0x50001000100030007000000010001000100090001000000070000060100000b0a else 0x1005000000202)) else (if i < 654 then (if i < 653 then 0xf00050001000100010005000500010005000d0100010101070608030a09 else 0x500010001000300070dc400010db000010dc0000100010802050001000a000102000d0b) else (if i < 655 then 0xb057200010e0000070005000501400dd20df40d5000070de200050df00001000300010140000906600001000100010310000d000300010001000500000102030008041a0816030f06160e14000b0205070b0215190b031c010b1e1f else 0x10e100e200001000100050e240001000100070140000100030001000100010108000300000206000201000001100e)))) else (if i < 664 then (if i < 660 then (if i < 658 then (if i < 657 then 0x3000700030030000100010005000706600007000300090013000701400001000700010007091102100302020106050001030008010600020101001416 else 0xe40000100030e600d72000d0e640e50000100090001000100050e30000b05820001015000070a100003015000010d600007015000010e700201000d020317030001060d02160013020718010201150f020b1410020b0e030a070c11061c25) else (if i < 659 then 0x10e80000000010001000300010e840001015000050e10000100010007000100010201010c0001030900030e000003110e else 0x15201000e9000010001000000050001000100010003000100030001000301020002050300060100020b0100000201020002010f15)) else (if i < 662 then (if i < 661 then 0xed20005000d0ee0059200030009000b0005000503200007000100010ea00007000300010eb000010ec401600160000305020100010c060001000515140402121704010a030f01060d040106090802001304011823 else 0x101600e8000010001000300010ef00001016000050e20000100010007000100010208010c0001030000030e000003110e) else (if i < 663 then 0x30001016400000005000500010005000500010005000500010001000b000500050007000500030c00110601020e05030e000904140d else 0x100200ea40e3000200f000ea00100000703))) else (if i < 668 then (if i < 666 then (if i < 665 then 0x10eb00eb400030660000300030007000300010e400003000300300003000300030003000302020005080b0602010000130b else 0xde0000100010e900de200070001010000010e920007000100010100080b00000207000d09) else (if i < 667 then 0x100400df00f1000400e600ec00103000703 else 0x500e0000010ee00e700ee40100000703)) else (if i < 670 then (if i < 669 then 0x70030001300110007000700030007000300070007003000030007000d0700040e05 else 0x70200004000010001000305) else (if i < 671 then 0x280000700500001020303 else 0x10f2000200f3001000000020505))))) else (if i < 688 then (if i < 680 then (if i < 676 then (if i < 674 then (if i < 673 then 0x200f200001000301 else 0x5002000000202) else (if i < 675 then 0x200f4003300f600f5001700040033201700002080603020105000909 else 0x3000101)) else (if i < 678 then (if i < 677 then 0xf800000002000050f700203000503 else 0x500200f7000020000000305) else (if i < 679 then 0x2000050f900002000303 else 0x50fa00fb00f90002000200fa201030000030705))) else (if i < 684 then (if i < 682 then (if i < 681 then 0x3002000000202 else 0x1002000000202) else (if i < 683 then 0x20018000010000000100000306 else 0x10fc00020020000000002000307)) else (if i < 686 then (if i < 685 then 0xf540f5001b000010340018003420fd0018000010806000204050002020000090d else 0x1800fc0000100200002000503) else (if i < 687 then 0x1002000000202 else 0xf64002003500f600fe001900050035201900002070703020105000909)))) else (if i < 696 then (if i < 692 then (if i < 690 then (if i < 689 then 0xd000101 else 0x1000110000003000300010ff0000500070000000100010a050300000b030200000400000c0d) else (if i < 691 then 0x10003000100000005000100010001000100030103000301010003020a09 else 0x2010140005000301)) else (if i < 694 then (if i < 693 then 0x71022002010201040000010300100000703 else 0x1002000000202) else (if i < 695 then 0x1002000000202 else 0xff20ff0000310600fe00030036001a001a001a001801050105403620a070004000000040e08))) else (if i < 700 then (if i < 698 then (if i < 697 then 0x1a001b000030003000300010007000304050000000500000007000000020000000811 else 0x1a0000300201060000003000000000407) else (if i < 699 then 0x1002000000202 else 0x107010500001000301)) else (if i < 702 then (if i < 701 then 0x7000b000510800005000100070005000500050005000800070308000b000301000b010c0e else 0xb000500010007000500090005000000010005000100030005000700130005010e000200090405000003020000100e) else (if i < 703 then 0x100010000000300050001000000010001000f020704010200040a07 else 0xb1074018000010001000103720001000301b00009107000070005000103700003028001b00030000510600001000101b001160006070a000607020006070007080d0200110701001117040f0109110f01160c06101211061927)))))) else (if i < 736 then (if i < 720 then (if i < 712 then (if i < 708 then (if i < 706 then (if i < 705 then 0x1a001b000030001000500070001000100010101030101000002000909 else 0x1000300050003000d00010001000101b01060000100010000020001050a07010200070107060401010200010d13) else (if i < 707 then 0x10fd002100200000303 else 0x500d40001000000070001000300030001000300030500010a000007000703010001030b0e)) else (if i < 710 then (if i < 709 then 0x7109010a410b000071092000710c0000b0007000700070005000700090a030300000100000e0a else 0x2310d000000202) else (if i < 711 then 0x26010e00005000500050007000b000500050005020100050202000909 else 0x700030030000710f400190007000710b0000f0011000300070500000000000b0000050c00000001090000040100020203050d19))) else (if i < 716 then (if i < 714 then (if i < 713 then 0x4000071100000000000304 else 0x701e01110000500070007000710e00007000700070007000f000700020200030e05) else (if i < 715 then 0x10005000500011124000100070001000100030001000007040300000100000b0a else 0x500010000000700030001000100010001000100010302010002020b05000c09)) else (if i < 718 then (if i < 717 then 0x1511400011001500210021000f116001c0000f10c400150007000700070007000f0011001b1010110003820c6000070c620007118009d010f00007117011321154113001c0001103800007051f211f0b0803191108030005081d08011a031612000308100203261b else 0x701c0000700070011000700070007001b000f000700070b0001060008010000010102000001050000040c13) else (if i < 719 then 0x11a0000b002300070011000501c000070260000100030001000001e00007000f119200070015111011900007000500070007000100100903000b081206150102170102100001010e000b020206000106030e011a1f else 0x10003000511b4000300030000000300070001000300030008040107030006050001020003000c0f)))) else (if i < 728 then (if i < 724 then (if i < 722 then (if i < 721 then 0x70000000100030005000000010001000d000101020000080100000101020b0b else 0x40000511c001010000000305) else (if i < 723 then 0x51184005002020001000305 else 0x10000000711d2000111d011e000010001000300050001000100040003030c030b0004010000010d0e)) else (if i < 726 then (if i < 725 then 0x29002110900011102000231214001101d0000f000f0007000b12040392001b000700071220123000210007001111f00007000f01d01240000d1a020001000b0c011702000101020010130608030116150301030e0f0103170a01060d05011c27 else 0x1270000b00071260000701d00007000701d00011125000070007000702030100010100060d00000d0105000e0f) else (if i < 727 then 0x50011000500050001000100000001000500050005002501d20005000f0001000500070005000300210302080306020201000a0e030004150e else 0x3b210a41030128003b012b01294002312a0000701e00029002100070015001b000700070021000f0007000f001100071160000710d00011000710000a000b000119000001150800071700120c1403121516001205180e120b1a0012081c06121d26))) else (if i < 732 then (if i < 730 then (if i < 729 then 0x71262001501e00011000712600007000712c000070007080300050204000000000003010000010400040c13 else 0xb00010003000501e4000012d001c4000100070005000500010001060605000102030d090a0a04000102040c000a04010b0204060702050503020e1f) else (if i < 731 then 0x12f000071304000303c2001112e40013000f0007000703c00007104000030030000701f0000301f0000301000102030a010003000e0c12000100140001000e0b010209000302070401001000011523 else 0x701f0000312c000070007000701f00015000700031270000300070011127200070007000700070007000305030000020100070c1609)) else (if i < 734 then (if i < 733 then 0x3000000030000000000010003000001f0000300070001000f00030d0606000003000104060205000e0d else 0x1320131000070001000013120000000100010001000300010001000100010005000106000006000007030300110a) else (if i < 735 then 0x11f00011000700300003128000070000000710b000070030000311f20007003000070007001b00070003110e030200030102040101000f03150e else 0x712161214004412e4000012940100000703))))) else (if i < 752 then (if i < 744 then (if i < 740 then (if i < 738 then (if i < 737 then 0xb1330000700070007122000070007000500000011000712d4122200150007000700070007000701c00007000710000315001705 else 0x712320040004012f0123000400103000703) else (if i < 739 then 0x712420050134012b0124000500103000703 else 0x1350136200300003000300070001000300030030020002020304010903000603000101020200050a13)) else (if i < 742 then (if i < 741 then 0x1350000f0630000313800007000300030013000313840003003000030660000300031370000300030010060c0006010c000109000003140e else 0x300007000300030003000700030302010403020204000709) else (if i < 743 then 0x300007000f000f001900070011000700070003000701020101010203040005060000000b0e else 0x13a010500200020006700003139000300672040004020009030705030407000000070b0c))) else (if i < 748 then (if i < 746 then (if i < 745 then 0x300070003000300030100000404000506 else 0x713b0000f13c00007000700030007003000030011000300190007003002010c060b070008000e030000010f0e) else (if i < 747 then 0x13c000300007000713f013d00003000713d20007001b003000070003000300190007000f000713e000110007000700070003010206000200000d0c0f0e09030e0106010e1503011915 else 0x3000300001404000300030030000300070003000300030003000301050303000c020e07)) else (if i < 750 then (if i < 749 then 0x70011000700300007001b00070003000700110030000700070007010003000000020c000d030006050e0e else 0x14100030028006800fe013a00682021004100007021013a4041202100c0200080105030e07) else (if i < 751 then 0x210000700030009000700030013142000030001001100070007000700000200070002000a0200080400010002010e12 else 0x3144000030005000000030007000100031430000300011444001301400001000300030003000100000d8000030003000300e000010814070a0209000c041b09)))) else (if i < 760 then (if i < 756 then (if i < 754 then (if i < 753 then 0x3000010003000300300003000f00030003000700030003000300030a01050001060e06 else 0xd000101) else (if i < 755 then 0x4002000003000301 else 0x300030003000301f00030000300030033000700030002020903070200000b09)) else (if i < 758 then (if i < 757 then 0x300030003003000030001003000030007000700030005000300020a000102000b0b else 0x700070007000b000700050003000101f000070007000100070b030101000302070008030101000e0e) else (if i < 759 then 0x1b0050000f0011000f0003000d14200007000f0019000f09000003010000000a00000000000a04090004060202000107000c1a else 0x5000100010007000100010003000001050000010707))) else (if i < 764 then (if i < 762 then (if i < 761 then 0x5000100000001000300010001000b01000001010000020100000601000106010811 else 0x1b00005000f0001000d000d0001000002000001010500040102040001000100010713) else (if i < 763 then 0x1000b00000007000100030005000700050005000000050001000508040000040102050301000e0b else 0x1004000000202)) else (if i < 766 then (if i < 765 then 0x28000500001000301 else 0x5004000000202) else (if i < 767 then 0x5005000000202 else 0x14500001004002000000020305)))))))) else (if i < 896 then (if i < 832 then (if i < 800 then (if i < 784 then (if i < 776 then (if i < 772 then (if i < 770 then (if i < 769 then 0x4000031460145000000100000405 else 0x3004000000202) else (if i < 771 then 0x5147000400100000303 else 0x1480147000070040004000000100000505)) else (if i < 774 then (if i < 773 then 0x149000050040000000000304 else 0x514900040000000000304) else (if i < 775 then 0x3004014a00200000303 else 0x14a0004000010200000303))) else (if i < 780 then (if i < 778 then (if i < 777 then 0x4200f40139014b0004402200040042202200002040703020106000909 else 0x1000101) else (if i < 779 then 0x3004000000202 else 0x1004000000202)) else (if i < 782 then (if i < 781 then 0x1004000000202 else 0xf60005014c014b0004002300430043202300002040703020106000909) else (if i < 783 then 0xd000101 else 0x10000000100050007000100030001000102010202050600000001090a)))) else (if i < 792 then (if i < 788 then (if i < 786 then (if i < 785 then 0x10001000514d400010003001100000003000100030003000301000101000002000004010004010d0e else 0x100030007000300050000000100010005000500030102050402020000050400000102000a11) else (if i < 787 then 0x500090001000500010000000700070001000314e0000700070001010500000200050301000204020e0d else 0x5000300010005000b0007000100050005000500050000000b090003040006000300010002060003040c12)) else (if i < 790 then (if i < 789 then 0x50001000b000700010005000100050000000000000100000000010000040103000912 else 0x1004000000202) else (if i < 791 then 0x1004000000202 else 0x10003000000030005000700030001020504030400060807))) else (if i < 796 then (if i < 794 then (if i < 793 then 0x3000000050001000100000001000100070001000d0001000100010300060d00020e06 else 0x5004000000202) else (if i < 795 then 0x1500151000000040000514f014f20000000703 else 0x1004000000202)) else (if i < 798 then (if i < 797 then 0x1004000000202 else 0x3000101) else (if i < 799 then 0x10005000100010003000100010001000100060301000907 else 0x15220007000b000100070005000313b000071540000701e000071530000701e40007152000070000000100000005000700010901120000010f000501000f0214190e))))) else (if i < 816 then (if i < 808 then (if i < 804 then (if i < 802 then (if i < 801 then 0x1f001115b013c015a000050f9015900240000b157000070240001b0ab00005154004600007003515521560000515c000050cd000070462000502401550000b0cd215800240000f000322050403140204031b050403000717000c0b0610210b1b0d1c071b0712041b071d1801090814012429 else 0x7000500050240000500050005000715d0000b00050005002300050800000d03020a000001050000010d00020e11) else (if i < 803 then 0x30001001300030003000115b0000300030005010401080100000002010001010a0d else 0x300070001000100000005000100010003000100010002010600000201000b09)) else (if i < 806 then (if i < 805 then 0x5000300010001000100000001000100010000020300010200000909 else 0x15c00000005000050050000501) else (if i < 807 then 0x50000000b0000001115f00005000b0009047214f015e000070cb400090250000514f400050250000513d000050cb000090250000f0fa000001601020d0a01160502051105020b10030c030a070205000f020f1205081c1f else 0x110001000000050001000100030252000100050001000000010003000100010007010204010102030509020e000002110e))) else (if i < 812 then (if i < 810 then (if i < 809 then 0x500050005000b000500050007162000051550025000050250000502500005161016000009000700050005000902000006090000050100000a10001610 else 0xca415d00482156016300ca2164015000ca01650000b0260001f0005000500230ac000051504000b114400050ca600110480000f000515d4001b000500070005000711400005000b000704230f000220061e02000d00171c0b1b13190f1d021902200019151202190f0c0119002202192526) else (if i < 811 then 0x1100070260000701c4001100010005000701c00001001b000f00031330000713e0000b00070009000713340005157000070000000f0007000513f0000702030113000f0f180206081800160500000a0a17020c1000040f201a else 0x1612000502600005000b000716601580000500050005000500050005161000050260000500050010000f000c0609010300050a0500000100001313)) else (if i < 814 then (if i < 813 then 0x159000001672000100010001000700011670000500011680000100010003050404050000010a000102060300010f0f else 0xcc0000515100003000f00111514001b000b0005169004a004a2000313f000050cc60003027000030cc200070cc400030fb00003000102070000021512140e01060516050605120f06010d050601000306050c01061923) else (if i < 815 then 0x1620000b00031622000500030270000500070005000502701660000300050000000515a00100000b0100080403020c030d09000001010503010100000a1219 else 0x1000302700000000300030003000d0005000f00030a030301000201000003020000030500000101000000020000020101000b1d)))) else (if i < 824 then (if i < 820 then (if i < 818 then (if i < 817 then 0x1000716a216a0000116b0000300010000000100010005000000010001000100060d04010006010100110a else 0x165016c015f2000515f015c00050030200000000000707) else (if i < 819 then 0x7000100010003000000050001000100010001000101640001000200020902000d07 else 0x90005000700010000000700070001000700030007000101f0020202030302050102020001000a0d0e)) else (if i < 822 then (if i < 821 then 0x101 else 0x101) else (if i < 823 then 0x3000302700003000301000101000505 else 0x7000b000500050005000500070001000900030000000b00070001000500050270010d0700000e030c000207000002110e))) else (if i < 828 then (if i < 826 then (if i < 825 then 0x3005000000202 else 0xf000f0001001b000f0001000f00030003000d00050001000f000501000501010c0b09010e09) else (if i < 827 then 0x500000001000100070001000100030001000100000201000502010200040b09 else 0x700090005000100030000003000090007000100010003000700030007000100070707100005010202000100110b)) else (if i < 830 then (if i < 829 then 0x5000100010007000100000002030300010000050a else 0x3000b00050005000500010000000100070004000400030004000700050000070400040504000100040918) else (if i < 831 then 0x1005000000202 else 0x16d0000d005002000000020305)))))) else (if i < 864 then (if i < 848 then (if i < 840 then (if i < 836 then (if i < 834 then (if i < 833 then 0x16d0000100500001000303 else 0xd005000000202) else (if i < 835 then 0x280000101b014c0028002800fd014c40280028004c204c00280000d01 else 0x2800000000d00500001005016e00000000703)) else (if i < 838 then (if i < 837 then 0xf16e00050000000000304 else 0x16f0000d0050000000000304) else (if i < 839 then 0x5016f00005000100000304 else 0x50001000d00110000000d000d000d000f000100010000000d030500020b05050d07))) else (if i < 844 then (if i < 842 then (if i < 841 then 0x1000500010000000000030001000105000001000001010006020000080d else 0x1142000000007000700010005000100010103000001030400000304070200090e) else (if i < 843 then 0xd0030000f000f000f000d0003000f001b000000070001000f000f0005000c0006030100060001000b020800000201000e15 else 0x50000000d000f000d000d0001000d0001000d000d0001050501030005040c07)) else (if i < 846 then (if i < 845 then 0x700010003000500010005000b000500050001020301000203000001000006020b0d else 0x1005000000202) else (if i < 847 then 0x1005000000202 else 0x1100154002001c0000001a00000002201500000012001900104018000f001600010005200b2014401700164009200b0004200f401940090003000a200840096014000820040007001d000c001a400e000a0013000940086008001000050006000d0001201b00032202a1e32132a1731022a0c030e2f002c232a3412)))) else (if i < 856 then (if i < 852 then (if i < 850 then (if i < 849 then 0x11000000320001000d000301e000a000840017000100700080020000100001005000900001000100b0001100010001006000010220000100030001009400400001000100100214000900050010021001f000050000000100100003000000050700002b1504030208040d200c00091d2212030e291a21060b1f142a2d1421301f else 0x34000000384044000200420002002300380002003500410031403b4032003900200031003f0037403a4003003b002c00300030403e402a0039403e0027403d0040003a002500280045002d003f402f002b00360028403c0029003300260027002e0037004300240202a1e32132a1731022a0c030e2f002c232a3412) else (if i < 851 then 0x4000584052005720001000104e004b0056000010001000504c2024204a0000105c005300001000f055000050003003005000480000105b00512000100010030050404900013051604d0000105a000050012000704f0000105d0000305800001046000030470000d05940540000505a4059000010030000109270425021c3728021033060900152e09341833092f20080f00010a0d00010c1300011d3a2624213b101c002d121c252e001c3c33 else 0x10062006f000c0067204b2064005e00040065006e00250000000010040001706800011061600010040000100010011060206d00001001700010001000d00010692000106a0000105f0000106c0000106b000130001001100010612001106e40011001306a40011066000010011000106b4000106300011000104270200023b272f1a2701002a001e3a222811320034170d062e0331222821380028153b06280c37262e3d2a)) else (if i < 854 then (if i < 853 then 0x7e4000305e0000f070205f0000307f0000500110732000f0720000507740540000502600003075007640710000307c000c0005007800005079000100050000304c007700003000f07600000000307b00740000907d0000f0744000f07e007a0000000030050000307540050005000010207260102292b200019000100010001021918012c3330132f24001008031d10361b0010250300201f0b0010160318053203003735 else 0x60009000462084008300910068008c008e000250003081000130010000908e4006008b00870086000120800000004600060000100010850085408a0000108900001006000010822000100010894002500010003000108d008f00820000108120001088000030001000d00010884000106020003000100290060000100252f3d390006320e281b261c0014000a3904020c361402072f0026052c20021e270402163a3202053c01023f2a) else (if i < 855 then 0x9e009400920093009b00964047208000470000000700070097009f009d0000009f400010960097409800025007000010001054000010001000100230810000109500009054009a00001001f0984001f0a000001001f00010990001f00100001099400010012000100010003002100010013000100700003000109c00001081200010001000d0940213e120024220139001a2a0807350e371332182c2b3a13080b340a08073c010811401e084326 else 0x2d0005002b0ab40005000500100a20000506a0050200050a700a40000f08800005000f0a840aa40025002500250af4000500050a540b00000f00050a92008000050b100ad6002b00800025000f0a320b20000500050ae0008000050a1000050005000f0000000501400612008000110b300ac4000f00050a600025000500050270380700002e0f08100a01180d0a401e3c212b2d012102002a0a23331a140f36100a4121))) else (if i < 860 then (if i < 858 then (if i < 857 then 0x510000100090bb00001000700050b50000d0280000b0a2007700001009000050b4601400001000300900ba000030001000700010bf000100bd00bc00001000309900b800003009000000005000100010b6200900001000100900a1000010b90000100050b7400900be000900001293230022e04011a0206012e1c060a140206280c1a110a082d00220f331e221436060114261d133727 else 0x1f0c4000010021082206c000010c5000010b04000101b000010562000500a00c00000108a000030c7000050c80000100a00c300023000500a00c9000a000030b0000010c20000d0c84000900a000130c62000100a000010c740c1000a0000300a00001000000a00010000102b000010ca2002f1b3721333434032f2e1c2800010209161c220f0a25082a040d2b1d020302130217120b1a2c02213a27) else (if i < 859 then 0xb0d840d7000010cb200030cf000010d900005000500010d1200b000b00c1000050001054000010d300d440cc000010d500ce000b00001000000010570001000b0000300010d400ba00003000d0c000ba400070d0002c000b00d2000090d6000070d2400070d8001b00cd0000100b000010d3407b000b000010239280102102e340029001200010001352900010201061533300016080521243a2b002010280024230b2d1a1d031b1e3703003c35 else 0x13001200db0000702d200c00db40011001b001300f00007001100c0005000070da000c00dc0005200c0000700e000f40013001301000007000f00c0000702d0004200c0000f000701100104004000130000000704000100240519142300190717000c1a270e1c022300081e0a201500000a01001300151a251d1c2a27)) else (if i < 862 then (if i < 861 then 0xed000d002e20ea00e040e1001e002e00c220e900bb60e340dd20e0000d00bb20e700df40e2400e00e300d500a420a460e640de00e140e600a440e500e800e2008300bb00ee001e20e7404a00c200d520bb40e400dd00de209d00a400eb00df00ec004a220231e321323172d02230c2a0e30002f2b233312 else 0x70f9000010fb40f30000107c0000d0fb000030620000300c00001000100010fa40ef0000100030001100000090f00000500030f400ff00520000100010f100f02000b00e00fc002f000070f800f2000050f7000e00005000707c20fe0000100e006220fd00001000100010f240ef2000700010f500e800fa000010f6000010f940f140540000500e0000102f204273f033e2c323f3132163b4501161a3a370217062e02132211240d0b461c330028244723) else (if i < 863 then 0x10c410a406a210d000c000f010f0014000050a5603020300107400f010401050102000050f10108410e0109010120a5410b400f006a01010110000000007000500f0103000310007001100050007106408500005000b0005001b000500050005000700310005000500050005000b00050005001f000f041f3736022222000336330008342b1b031800000d1d0000001e021a1134291a1827021a0913021a022f041a1528171a0a30321a3b34 else 0x102011c00007000f1142054011140007010000071130002311d00021117400071120010007700f2011a00007001b10300015001101000007119000c011f0000703101140031200291122001100210007115001000007000701400772000f11e01180000711320007010011b01160000f0000000700110000010012000f022432382c3b242202002101040500010202123802120f000409131f04353231042c121d2509042a2e230a1b182312370a233e33))))) else (if i < 880 then (if i < 872 then (if i < 868 then (if i < 866 then (if i < 865 then 0x12b001f0011006401222034011c40bc212501240121212c010540a7212a012200bc612600bc009e0124403420f60129012100a7606420a70086001f2125404f21294123012700a741050065206500f5004f012a40da012800bc411c007d207d0011012642631100120291d0100132801092c14011b0a0701121c30013218 else 0x662133001b00c320c3006c00120035206c201101334000012e00120135001200d62132412d210d40f70134013100120012013140350132000c0130010d013040d60012006600120000300030003000f00030003000f0007000f12d0000700031230000312f00003000700070007000300030003000300130007152d07150109000b00193b330835142c0414072e042d10270424051f0336051d00190922132513280e2f0535031b3d2e) else (if i < 867 then 0x13620007000b00c0000313a0000300050362000100031380138401300130139412f00005036007b200010003013000010f800001137011b000000001013001b001300001136000010000000d000907b0000712e011b40007000113902c060029190600001906001a071400080710001a1620010e290828240d2300190d0c1e1c0d0c1b0a0d0c15050d08130a0d18250a0d2e35 else 0x372009201400005001b000f009000f00df00007000500250082000b01a0002300070190000b0005001f01640005000b037001400005000513b0018000070005008001400140001113c00005124001700005000501000000000b000500050c00000a02290a000c0912000c2a0028141f19180d0116210c24261015252e000c2f21)) else (if i < 870 then (if i < 869 then 0x14b0000014a013f0149013900d800be21430000013e2000007e013e0146003820580148013000c700b221420038013d2125006e013d00d8214500f9011f00be007e209f014100e0013b0021014c001600c721440021210f00b2006e208e014000db00150015014700582241e0a02171104020d33310200250f023510 else 0x314f01500054000030007151015a01590000f1060000515b013f00013000300030003052000050005126000070bd600071570000b0e100bd403900aa20005158000030144152014740011016015501530000511d400050aa000030392156015400003016014d214d000030005000714e214e00003212d003202073401370f2501381b0401020b14312e2908002d2a0800162708001d2908051f030805182908000c00143b2f) else (if i < 871 then 0x15f0157003c2001b000515c2000501400170000700050005017008f01600162000070005000715e00005014415f4127000110e40000b1574000b000715c0000503c0002300051090000b15d0000510740035017000050ae200051070000f1610000000050ae0001f16300005331d2022011d2a020126000f012b090201261016062d31020e070109290d27000c0f34000c141a090c0015190c001c230c1833090c3635 else 0x14015800ab600000ab216c0054016d00e5016601652000b03d016e00144018011e015e015f41642166215f01680165003d201800b8016401670018001800ab00b82128016a011e40ab4158416f0000500110005018016900007000500050007002309000005000b0005001b0005000716b000070005000500050005000b00050005001f000f0427403d042a2d2e023e15001130313c033937060c3b0000001c021810410218121d02180320021802363725193a0918092a15244334))) else (if i < 876 then (if i < 874 then (if i < 873 then 0xe6001401310170217100b0200030000001b000310d0175403e0003317740003019017001740000f0b00176003e2172014800ac40ac60190159401b01610000b01900003019001900003000300051730000300070003019000030003000700050003001100030218082d032701030200022b050004292900002a052d252405071f1d0207061a000711160c10022600120a320922061c050f3332 else 0x132011b0179003f0000100010140000b000d0003000115a401a000030e7001b017a40005178000010ba00007000103f201a0173000050001000500010ba216e001a0000917c0000000011782000101a0172017b40001000114901c29002a030016290300001700030019032407000d0200230d02001503240a19051f000f0502211005021c190502290114021e170c231506052d39) else (if i < 875 then 0x130012000b001a400a00000019401d001a0019014a001b014a40430000100b20009000100a20ec00007000704320001000100070005000300030001000100010005000b0001000d01200200041f0200121e0000031c0014141a0214141a001c061808190618011703180416011801100f18070d0b18242e else 0x14b013c4022014b4120413c0184007f204420440110415b0183006f20b360b34110015b4091006f0022217f005d20bf60bf4120018000a0007f00dc00ed001d0163018340b320b3017d2181017d00000100016f018440bf20bf017e2182017e001c005d026313001202e2c0100281d0109131401120a1c011b292f013218)) else (if i < 878 then (if i < 877 then 0xd92000f1760000d0520000f000d18801862000f045201d0054017c4000d0c92185217c0000d01d0000f0450000d13a0000f01b018701850000d000d000d189418a4001b000d000d14c017f00c90000f1764000d0d90000d18c0000d14c418900ee0000d18b0000d1340000f01d018a01860000f01d0000f0134091f16250532171d051f0d00300a2608280a0b023010220a0532310e013c1f else 0x1100154002001c0000001a00000002201500000012001900104018000f001600010005200b2014401700164009200b0004200f401940090003000a200840096014000820040007001d000c001a400e000a0013000940086008001000050006000d0001201b00032202a1e32132a1731022a0c030e2f002c232a3412) else 0))) else 0))) else 0)))

def nsE : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 9
  | 5 => 72
  | 6 => 368
  | 7 => 397
  | 8 => 30
  | 9 => 1
  | _ => 0

def offE : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 10
  | 6 => 82
  | 7 => 450
  | 8 => 847
  | 9 => 877
  | _ => 0

def stateE (s i : Nat) := rowsE (offE s + i)

def actionE (s i h : Nat) : Nat :=
  let t := segE (offE s + i)
  let a := t &&& 255
  let b := (t >>> 8) &&& 255
  let d := (t >>> (16 + 8 * (h % a))) &&& 255
  (t >>> (16 + 8 * a + 16 * ((h / a + d) % b))) &&& 65535

def rotateE (g : Nat) (ws : List Nat) : List Nat := match g with
  | 1 => ws.map (blockWord 36 [1, 0, 3, 2, 5, 4, 7, 6])
  | 2 => ws.map (blockWord 36 [2, 3, 0, 1, 6, 7, 4, 5])
  | 3 => ws.map (blockWord 36 [3, 2, 1, 0, 7, 6, 5, 4])
  | _ => ws

theorem rotateE_ok (g : Nat) {s ws} (h : NatRun (mask 144) (goal 144) s ws) :
    NatRun (mask 144) (goal 144) s (rotateE g ws) := by
  unfold rotateE
  split <;> first | exact h | apply block_run h _ _ (by decide +kernel) (by decide +kernel)

def Z (s : Nat) := barrier 144 stateE nsE actionE sixE rotateE s

theorem h3y0 : span (Z 3) 1 0 = true := by decide +kernel
theorem z3 : span (Z 3) 1 0 = true := h3y0

theorem h4y0 : span (Z 4) 6 0 = true := by decide +kernel
theorem h4y1 : span (Z 4) 3 6 = true := by decide +kernel
theorem z4 : span (Z 4) 9 0 = true := (@span_join (Z 4) 6 0 3 h4y0 h4y1)

theorem h5y0 : span (Z 5) 6 0 = true := by decide +kernel
theorem h5y1 : span (Z 5) 6 6 = true := by decide +kernel
theorem h5y2 : span (Z 5) 6 12 = true := by decide +kernel
theorem h5y3 : span (Z 5) 6 18 = true := by decide +kernel
theorem h5y4 : span (Z 5) 6 24 = true := by decide +kernel
theorem h5y5 : span (Z 5) 6 30 = true := by decide +kernel
theorem h5y6 : span (Z 5) 6 36 = true := by decide +kernel
theorem h5y7 : span (Z 5) 6 42 = true := by decide +kernel
theorem h5y8 : span (Z 5) 6 48 = true := by decide +kernel
theorem h5y9 : span (Z 5) 6 54 = true := by decide +kernel
theorem h5y10 : span (Z 5) 6 60 = true := by decide +kernel
theorem h5y11 : span (Z 5) 6 66 = true := by decide +kernel
theorem z5 : span (Z 5) 72 0 = true := (@span_join (Z 5) 36 0 36 (@span_join (Z 5) 18 0 18 (@span_join (Z 5) 6 0 12 h5y0 (@span_join (Z 5) 6 6 6 h5y1 h5y2)) (@span_join (Z 5) 6 18 12 h5y3 (@span_join (Z 5) 6 24 6 h5y4 h5y5))) (@span_join (Z 5) 18 36 18 (@span_join (Z 5) 6 36 12 h5y6 (@span_join (Z 5) 6 42 6 h5y7 h5y8)) (@span_join (Z 5) 6 54 12 h5y9 (@span_join (Z 5) 6 60 6 h5y10 h5y11))))

theorem h6y0 : span (Z 6) 6 0 = true := by decide +kernel
theorem h6y1 : span (Z 6) 6 6 = true := by decide +kernel
theorem h6y2 : span (Z 6) 6 12 = true := by decide +kernel
theorem h6y3 : span (Z 6) 6 18 = true := by decide +kernel
theorem h6y4 : span (Z 6) 6 24 = true := by decide +kernel
theorem h6y5 : span (Z 6) 6 30 = true := by decide +kernel
theorem h6y6 : span (Z 6) 6 36 = true := by decide +kernel
theorem h6y7 : span (Z 6) 6 42 = true := by decide +kernel
theorem h6y8 : span (Z 6) 6 48 = true := by decide +kernel
theorem h6y9 : span (Z 6) 6 54 = true := by decide +kernel
theorem h6y10 : span (Z 6) 6 60 = true := by decide +kernel
theorem h6y11 : span (Z 6) 6 66 = true := by decide +kernel
theorem h6y12 : span (Z 6) 6 72 = true := by decide +kernel
theorem h6y13 : span (Z 6) 6 78 = true := by decide +kernel
theorem h6y14 : span (Z 6) 6 84 = true := by decide +kernel
theorem h6y15 : span (Z 6) 6 90 = true := by decide +kernel
theorem h6y16 : span (Z 6) 6 96 = true := by decide +kernel
theorem h6y17 : span (Z 6) 6 102 = true := by decide +kernel
theorem h6y18 : span (Z 6) 6 108 = true := by decide +kernel
theorem h6y19 : span (Z 6) 6 114 = true := by decide +kernel
theorem h6y20 : span (Z 6) 6 120 = true := by decide +kernel
theorem h6y21 : span (Z 6) 6 126 = true := by decide +kernel
theorem h6y22 : span (Z 6) 6 132 = true := by decide +kernel
theorem h6y23 : span (Z 6) 6 138 = true := by decide +kernel
theorem h6y24 : span (Z 6) 6 144 = true := by decide +kernel
theorem h6y25 : span (Z 6) 6 150 = true := by decide +kernel
theorem h6y26 : span (Z 6) 6 156 = true := by decide +kernel
theorem h6y27 : span (Z 6) 6 162 = true := by decide +kernel
theorem h6y28 : span (Z 6) 6 168 = true := by decide +kernel
theorem h6y29 : span (Z 6) 6 174 = true := by decide +kernel
theorem h6y30 : span (Z 6) 6 180 = true := by decide +kernel
theorem h6y31 : span (Z 6) 6 186 = true := by decide +kernel
theorem h6y32 : span (Z 6) 6 192 = true := by decide +kernel
theorem h6y33 : span (Z 6) 6 198 = true := by decide +kernel
theorem h6y34 : span (Z 6) 6 204 = true := by decide +kernel
theorem h6y35 : span (Z 6) 6 210 = true := by decide +kernel
theorem h6y36 : span (Z 6) 6 216 = true := by decide +kernel
theorem h6y37 : span (Z 6) 6 222 = true := by decide +kernel
theorem h6y38 : span (Z 6) 6 228 = true := by decide +kernel
theorem h6y39 : span (Z 6) 6 234 = true := by decide +kernel
theorem h6y40 : span (Z 6) 6 240 = true := by decide +kernel
theorem h6y41 : span (Z 6) 6 246 = true := by decide +kernel
theorem h6y42 : span (Z 6) 6 252 = true := by decide +kernel
theorem h6y43 : span (Z 6) 6 258 = true := by decide +kernel
theorem h6y44 : span (Z 6) 6 264 = true := by decide +kernel
theorem h6y45 : span (Z 6) 6 270 = true := by decide +kernel
theorem h6y46 : span (Z 6) 6 276 = true := by decide +kernel
theorem h6y47 : span (Z 6) 6 282 = true := by decide +kernel
theorem h6y48 : span (Z 6) 6 288 = true := by decide +kernel
theorem h6y49 : span (Z 6) 6 294 = true := by decide +kernel
theorem h6y50 : span (Z 6) 6 300 = true := by decide +kernel
theorem h6y51 : span (Z 6) 6 306 = true := by decide +kernel
theorem h6y52 : span (Z 6) 6 312 = true := by decide +kernel
theorem h6y53 : span (Z 6) 6 318 = true := by decide +kernel
theorem h6y54 : span (Z 6) 6 324 = true := by decide +kernel
theorem h6y55 : span (Z 6) 6 330 = true := by decide +kernel
theorem h6y56 : span (Z 6) 6 336 = true := by decide +kernel
theorem h6y57 : span (Z 6) 6 342 = true := by decide +kernel
theorem h6y58 : span (Z 6) 6 348 = true := by decide +kernel
theorem h6y59 : span (Z 6) 6 354 = true := by decide +kernel
theorem h6y60 : span (Z 6) 6 360 = true := by decide +kernel
theorem h6y61 : span (Z 6) 2 366 = true := by decide +kernel
theorem z6 : span (Z 6) 368 0 = true := (@span_join (Z 6) 186 0 182 (@span_join (Z 6) 90 0 96 (@span_join (Z 6) 42 0 48 (@span_join (Z 6) 18 0 24 (@span_join (Z 6) 6 0 12 h6y0 (@span_join (Z 6) 6 6 6 h6y1 h6y2)) (@span_join (Z 6) 12 18 12 (@span_join (Z 6) 6 18 6 h6y3 h6y4) (@span_join (Z 6) 6 30 6 h6y5 h6y6))) (@span_join (Z 6) 24 42 24 (@span_join (Z 6) 12 42 12 (@span_join (Z 6) 6 42 6 h6y7 h6y8) (@span_join (Z 6) 6 54 6 h6y9 h6y10)) (@span_join (Z 6) 12 66 12 (@span_join (Z 6) 6 66 6 h6y11 h6y12) (@span_join (Z 6) 6 78 6 h6y13 h6y14)))) (@span_join (Z 6) 48 90 48 (@span_join (Z 6) 24 90 24 (@span_join (Z 6) 12 90 12 (@span_join (Z 6) 6 90 6 h6y15 h6y16) (@span_join (Z 6) 6 102 6 h6y17 h6y18)) (@span_join (Z 6) 12 114 12 (@span_join (Z 6) 6 114 6 h6y19 h6y20) (@span_join (Z 6) 6 126 6 h6y21 h6y22))) (@span_join (Z 6) 24 138 24 (@span_join (Z 6) 12 138 12 (@span_join (Z 6) 6 138 6 h6y23 h6y24) (@span_join (Z 6) 6 150 6 h6y25 h6y26)) (@span_join (Z 6) 12 162 12 (@span_join (Z 6) 6 162 6 h6y27 h6y28) (@span_join (Z 6) 6 174 6 h6y29 h6y30))))) (@span_join (Z 6) 90 186 92 (@span_join (Z 6) 42 186 48 (@span_join (Z 6) 18 186 24 (@span_join (Z 6) 6 186 12 h6y31 (@span_join (Z 6) 6 192 6 h6y32 h6y33)) (@span_join (Z 6) 12 204 12 (@span_join (Z 6) 6 204 6 h6y34 h6y35) (@span_join (Z 6) 6 216 6 h6y36 h6y37))) (@span_join (Z 6) 24 228 24 (@span_join (Z 6) 12 228 12 (@span_join (Z 6) 6 228 6 h6y38 h6y39) (@span_join (Z 6) 6 240 6 h6y40 h6y41)) (@span_join (Z 6) 12 252 12 (@span_join (Z 6) 6 252 6 h6y42 h6y43) (@span_join (Z 6) 6 264 6 h6y44 h6y45)))) (@span_join (Z 6) 48 276 44 (@span_join (Z 6) 24 276 24 (@span_join (Z 6) 12 276 12 (@span_join (Z 6) 6 276 6 h6y46 h6y47) (@span_join (Z 6) 6 288 6 h6y48 h6y49)) (@span_join (Z 6) 12 300 12 (@span_join (Z 6) 6 300 6 h6y50 h6y51) (@span_join (Z 6) 6 312 6 h6y52 h6y53))) (@span_join (Z 6) 24 324 20 (@span_join (Z 6) 12 324 12 (@span_join (Z 6) 6 324 6 h6y54 h6y55) (@span_join (Z 6) 6 336 6 h6y56 h6y57)) (@span_join (Z 6) 12 348 8 (@span_join (Z 6) 6 348 6 h6y58 h6y59) (@span_join (Z 6) 6 360 2 h6y60 h6y61))))))

theorem h7y0 : span (Z 7) 6 0 = true := by decide +kernel
theorem h7y1 : span (Z 7) 6 6 = true := by decide +kernel
theorem h7y2 : span (Z 7) 6 12 = true := by decide +kernel
theorem h7y3 : span (Z 7) 6 18 = true := by decide +kernel
theorem h7y4 : span (Z 7) 6 24 = true := by decide +kernel
theorem h7y5 : span (Z 7) 6 30 = true := by decide +kernel
theorem h7y6 : span (Z 7) 6 36 = true := by decide +kernel
theorem h7y7 : span (Z 7) 6 42 = true := by decide +kernel
theorem h7y8 : span (Z 7) 6 48 = true := by decide +kernel
theorem h7y9 : span (Z 7) 6 54 = true := by decide +kernel
theorem h7y10 : span (Z 7) 6 60 = true := by decide +kernel
theorem h7y11 : span (Z 7) 6 66 = true := by decide +kernel
theorem h7y12 : span (Z 7) 6 72 = true := by decide +kernel
theorem h7y13 : span (Z 7) 6 78 = true := by decide +kernel
theorem h7y14 : span (Z 7) 6 84 = true := by decide +kernel
theorem h7y15 : span (Z 7) 6 90 = true := by decide +kernel
theorem h7y16 : span (Z 7) 6 96 = true := by decide +kernel
theorem h7y17 : span (Z 7) 6 102 = true := by decide +kernel
theorem h7y18 : span (Z 7) 6 108 = true := by decide +kernel
theorem h7y19 : span (Z 7) 6 114 = true := by decide +kernel
theorem h7y20 : span (Z 7) 6 120 = true := by decide +kernel
theorem h7y21 : span (Z 7) 6 126 = true := by decide +kernel
theorem h7y22 : span (Z 7) 6 132 = true := by decide +kernel
theorem h7y23 : span (Z 7) 6 138 = true := by decide +kernel
theorem h7y24 : span (Z 7) 6 144 = true := by decide +kernel
theorem h7y25 : span (Z 7) 6 150 = true := by decide +kernel
theorem h7y26 : span (Z 7) 6 156 = true := by decide +kernel
theorem h7y27 : span (Z 7) 6 162 = true := by decide +kernel
theorem h7y28 : span (Z 7) 6 168 = true := by decide +kernel
theorem h7y29 : span (Z 7) 6 174 = true := by decide +kernel
theorem h7y30 : span (Z 7) 6 180 = true := by decide +kernel
theorem h7y31 : span (Z 7) 6 186 = true := by decide +kernel
theorem h7y32 : span (Z 7) 6 192 = true := by decide +kernel
theorem h7y33 : span (Z 7) 6 198 = true := by decide +kernel
theorem h7y34 : span (Z 7) 6 204 = true := by decide +kernel
theorem h7y35 : span (Z 7) 6 210 = true := by decide +kernel
theorem h7y36 : span (Z 7) 6 216 = true := by decide +kernel
theorem h7y37 : span (Z 7) 6 222 = true := by decide +kernel
theorem h7y38 : span (Z 7) 6 228 = true := by decide +kernel
theorem h7y39 : span (Z 7) 6 234 = true := by decide +kernel
theorem h7y40 : span (Z 7) 6 240 = true := by decide +kernel
theorem h7y41 : span (Z 7) 6 246 = true := by decide +kernel
theorem h7y42 : span (Z 7) 6 252 = true := by decide +kernel
theorem h7y43 : span (Z 7) 6 258 = true := by decide +kernel
theorem h7y44 : span (Z 7) 6 264 = true := by decide +kernel
theorem h7y45 : span (Z 7) 6 270 = true := by decide +kernel
theorem h7y46 : span (Z 7) 6 276 = true := by decide +kernel
theorem h7y47 : span (Z 7) 6 282 = true := by decide +kernel
theorem h7y48 : span (Z 7) 6 288 = true := by decide +kernel
theorem h7y49 : span (Z 7) 6 294 = true := by decide +kernel
theorem h7y50 : span (Z 7) 6 300 = true := by decide +kernel
theorem h7y51 : span (Z 7) 6 306 = true := by decide +kernel
theorem h7y52 : span (Z 7) 6 312 = true := by decide +kernel
theorem h7y53 : span (Z 7) 6 318 = true := by decide +kernel
theorem h7y54 : span (Z 7) 6 324 = true := by decide +kernel
theorem h7y55 : span (Z 7) 6 330 = true := by decide +kernel
theorem h7y56 : span (Z 7) 6 336 = true := by decide +kernel
theorem h7y57 : span (Z 7) 6 342 = true := by decide +kernel
theorem h7y58 : span (Z 7) 6 348 = true := by decide +kernel
theorem h7y59 : span (Z 7) 6 354 = true := by decide +kernel
theorem h7y60 : span (Z 7) 6 360 = true := by decide +kernel
theorem h7y61 : span (Z 7) 6 366 = true := by decide +kernel
theorem h7y62 : span (Z 7) 6 372 = true := by decide +kernel
theorem h7y63 : span (Z 7) 6 378 = true := by decide +kernel
theorem h7y64 : span (Z 7) 6 384 = true := by decide +kernel
theorem h7y65 : span (Z 7) 6 390 = true := by decide +kernel
theorem h7y66 : span (Z 7) 1 396 = true := by decide +kernel
theorem z7 : span (Z 7) 397 0 = true := (@span_join (Z 7) 198 0 199 (@span_join (Z 7) 96 0 102 (@span_join (Z 7) 48 0 48 (@span_join (Z 7) 24 0 24 (@span_join (Z 7) 12 0 12 (@span_join (Z 7) 6 0 6 h7y0 h7y1) (@span_join (Z 7) 6 12 6 h7y2 h7y3)) (@span_join (Z 7) 12 24 12 (@span_join (Z 7) 6 24 6 h7y4 h7y5) (@span_join (Z 7) 6 36 6 h7y6 h7y7))) (@span_join (Z 7) 24 48 24 (@span_join (Z 7) 12 48 12 (@span_join (Z 7) 6 48 6 h7y8 h7y9) (@span_join (Z 7) 6 60 6 h7y10 h7y11)) (@span_join (Z 7) 12 72 12 (@span_join (Z 7) 6 72 6 h7y12 h7y13) (@span_join (Z 7) 6 84 6 h7y14 h7y15)))) (@span_join (Z 7) 48 96 54 (@span_join (Z 7) 24 96 24 (@span_join (Z 7) 12 96 12 (@span_join (Z 7) 6 96 6 h7y16 h7y17) (@span_join (Z 7) 6 108 6 h7y18 h7y19)) (@span_join (Z 7) 12 120 12 (@span_join (Z 7) 6 120 6 h7y20 h7y21) (@span_join (Z 7) 6 132 6 h7y22 h7y23))) (@span_join (Z 7) 24 144 30 (@span_join (Z 7) 12 144 12 (@span_join (Z 7) 6 144 6 h7y24 h7y25) (@span_join (Z 7) 6 156 6 h7y26 h7y27)) (@span_join (Z 7) 12 168 18 (@span_join (Z 7) 6 168 6 h7y28 h7y29) (@span_join (Z 7) 6 180 12 h7y30 (@span_join (Z 7) 6 186 6 h7y31 h7y32)))))) (@span_join (Z 7) 102 198 97 (@span_join (Z 7) 48 198 54 (@span_join (Z 7) 24 198 24 (@span_join (Z 7) 12 198 12 (@span_join (Z 7) 6 198 6 h7y33 h7y34) (@span_join (Z 7) 6 210 6 h7y35 h7y36)) (@span_join (Z 7) 12 222 12 (@span_join (Z 7) 6 222 6 h7y37 h7y38) (@span_join (Z 7) 6 234 6 h7y39 h7y40))) (@span_join (Z 7) 24 246 30 (@span_join (Z 7) 12 246 12 (@span_join (Z 7) 6 246 6 h7y41 h7y42) (@span_join (Z 7) 6 258 6 h7y43 h7y44)) (@span_join (Z 7) 12 270 18 (@span_join (Z 7) 6 270 6 h7y45 h7y46) (@span_join (Z 7) 6 282 12 h7y47 (@span_join (Z 7) 6 288 6 h7y48 h7y49))))) (@span_join (Z 7) 48 300 49 (@span_join (Z 7) 24 300 24 (@span_join (Z 7) 12 300 12 (@span_join (Z 7) 6 300 6 h7y50 h7y51) (@span_join (Z 7) 6 312 6 h7y52 h7y53)) (@span_join (Z 7) 12 324 12 (@span_join (Z 7) 6 324 6 h7y54 h7y55) (@span_join (Z 7) 6 336 6 h7y56 h7y57))) (@span_join (Z 7) 24 348 25 (@span_join (Z 7) 12 348 12 (@span_join (Z 7) 6 348 6 h7y58 h7y59) (@span_join (Z 7) 6 360 6 h7y60 h7y61)) (@span_join (Z 7) 12 372 13 (@span_join (Z 7) 6 372 6 h7y62 h7y63) (@span_join (Z 7) 6 384 7 h7y64 (@span_join (Z 7) 6 390 1 h7y65 h7y66)))))))

theorem h8y0 : span (Z 8) 6 0 = true := by decide +kernel
theorem h8y1 : span (Z 8) 6 6 = true := by decide +kernel
theorem h8y2 : span (Z 8) 6 12 = true := by decide +kernel
theorem h8y3 : span (Z 8) 6 18 = true := by decide +kernel
theorem h8y4 : span (Z 8) 6 24 = true := by decide +kernel
theorem z8 : span (Z 8) 30 0 = true := (@span_join (Z 8) 12 0 18 (@span_join (Z 8) 6 0 6 h8y0 h8y1) (@span_join (Z 8) 6 12 12 h8y2 (@span_join (Z 8) 6 18 6 h8y3 h8y4)))

theorem h9y0 : span (Z 9) 1 0 = true := by decide +kernel
theorem z9 : span (Z 9) 1 0 = true := h9y0

theorem checkedE (s : Nat) (hs : s ≤ 9) : ∀ i < nsE s, Z s i = true := by
  interval_cases s
  · exact fun i hi => absurd hi (Nat.not_lt_zero i)
  · exact fun i hi => absurd hi (Nat.not_lt_zero i)
  · exact fun i hi => absurd hi (Nat.not_lt_zero i)
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : NatRun (mask 144) (goal 144) s xs9953) : False := by
  have h9 : NatRun (mask 144) (goal 144) 9 xs9953 := extend_run h hs
  have p : xs9953.Perm (stateE 9 0) := by decide +kernel
  exact barrier_all rotateE_ok checkedE 9 (by decide) 0 (by decide) (Run.perm p h9)

def witness : Circuit :=
  { gates := [{ op := .or, inputs := [1, 5] },
      { op := .and, inputs := [0, 6] },
      { op := .and, inputs := [1, 5] },
      { op := .or, inputs := [7, 8] },
      { op := .or, inputs := [0, 4] },
      { op := .or, inputs := [2, 3] },
      { op := .and, inputs := [10, 11] },
      { op := .and, inputs := [2, 3] },
      { op := .or, inputs := [12, 13] },
      { op := .or, inputs := [9, 14] }],
    output := 15 }

theorem legal_witness : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem eval_witness_fast : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = f9953Fast x := by
  decide +kernel

theorem eval_witness : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = f9953 x := by
  rw [f9953_eq]; exact eval_witness_fast

theorem upper : HasCircuitSize 6 f9953 10 :=
  ⟨witness, legal_witness, by decide, eval_witness⟩

end PEqualNP.Outside.V_meta_9953__k10

open PEqualNP.Outside.V_meta_9953__k10 in
theorem PEqualNP.Outside.V_meta_9953__k10 :
    PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (18446461426206309032 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 10 ∧
      ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (18446461426206309032 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 10 ≤ t := by
  refine ⟨upper, ?_⟩
  intro t ht
  by_contra! hlt
  obtain ⟨C, hfan, hsize, heval⟩ := ht
  exact main9953 noRunFull ⟨C, hfan, by omega, heval⟩
