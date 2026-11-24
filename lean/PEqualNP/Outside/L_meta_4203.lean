import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4203

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wireMap (n : ℕ) (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

def gateMap (n : ℕ) (σ : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wireMap n σ)⟩

def circuitMap (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gateMap n σ), wireMap n σ C.output⟩

lemma wireMap_fin (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    wireMap n σ i.val = (σ i).val := by
  simp [wireMap, i.isLt]

lemma wireMap_ge (n : ℕ) (σ : Equiv.Perm (Fin n)) {w : ℕ} (hw : n ≤ w) :
    wireMap n σ w = w := by
  simp [wireMap, Nat.not_lt.mpr hw]

lemma wireMap_lt (n : ℕ) (σ : Equiv.Perm (Fin n)) {w k : ℕ} (hw : w < n + k) :
    wireMap n σ w < n + k := by
  unfold wireMap
  split_ifs with h
  · exact lt_of_lt_of_le (σ ⟨w, h⟩).isLt (Nat.le_add_right n k)
  · exact hw

lemma wireMap_inj (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (wireMap n σ) := by
  intro a b hab
  unfold wireMap at hab
  split_ifs at hab with ha hb hb
  · have hσ : σ ⟨a, ha⟩ = σ ⟨b, hb⟩ := Fin.ext hab
    exact congrArg Fin.val (σ.injective hσ)
  · have hlt : (σ ⟨a, ha⟩).val < n := (σ ⟨a, ha⟩).isLt
    omega
  · have hlt : (σ ⟨b, hb⟩).val < n := (σ ⟨b, hb⟩).isLt
    omega
  · exact hab

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_append_left' (w : List Bool) (b : Bool) {u : ℕ} (hu : u < w.length) :
    (w ++ [b]).getD u false = w.getD u false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]

lemma getD_append_eq' (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ge_len (w : List Bool) {u : ℕ} (hu : w.length ≤ u) :
    w.getD u false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hu]

lemma foldl_wireMap (n : ℕ) (σ : Equiv.Perm (Fin n)) (gs : List Gate) :
    ∀ (w w' : List Bool),
      w.length = w'.length →
      n ≤ w.length →
      (∀ u : ℕ, w'.getD (wireMap n σ u) false = w.getD u false) →
      ((gs.map (gateMap n σ)).foldl stepWire w').length = (gs.foldl stepWire w).length ∧
      ∀ u : ℕ, ((gs.map (gateMap n σ)).foldl stepWire w').getD (wireMap n σ u) false =
        (gs.foldl stepWire w).getD u false := by
  induction gs with
  | nil =>
    intro w w' hlen _ hinv
    exact ⟨hlen.symm, hinv⟩
  | cons g gs ih =>
    intro w w' hlen hn hinv
    simp only [List.map_cons, List.foldl_cons]
    have heval : (gateMap n σ g).op.eval ((gateMap n σ g).inputs.map fun i => w'.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [gateMap, List.map_map]
      congr 1
      exact List.map_congr_left fun u _ => hinv u
    have hstep_len : (stepWire w g).length = (stepWire w' (gateMap n σ g)).length := by
      simp [stepWire, hlen]
    have hstep_n : n ≤ (stepWire w g).length := by
      simp only [stepWire, List.length_append, List.length_singleton]
      omega
    have hstep_inv : ∀ u : ℕ,
        (stepWire w' (gateMap n σ g)).getD (wireMap n σ u) false =
          (stepWire w g).getD u false := by
      intro u
      simp only [stepWire, heval]
      by_cases hu : u < n
      · have h1 : wireMap n σ u < w'.length := by
          unfold wireMap
          rw [dite_eq_left hu]
          have := (σ ⟨u, hu⟩).isLt
          omega
        have h2 : u < w.length := by omega
        rw [getD_append_left' w' _ h1, getD_append_left' w _ h2]
        exact hinv u
      · have hge : n ≤ u := Nat.le_of_not_lt hu
        have hw : wireMap n σ u = u := wireMap_ge n σ hge
        rw [hw]
        rcases Nat.lt_trichotomy u w.length with hlt | heq | hgt
        · have hlt' : u < w'.length := by omega
          rw [getD_append_left' w' _ hlt', getD_append_left' w _ hlt]
          have hu' := hinv u
          rw [hw] at hu'
          exact hu'
        · have heq' : u = w'.length := by omega
          rw [heq', getD_append_eq', ← heq', heq, getD_append_eq']
        · have hg1 : (w' ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length ≤ u := by
            simp only [List.length_append, List.length_singleton]
            omega
          have hg2 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length ≤ u := by
            simp only [List.length_append, List.length_singleton]
            omega
          rw [getD_ge_len _ hg1, getD_ge_len _ hg2]
    exact ih (stepWire w g) (stepWire w' (gateMap n σ g)) hstep_len hstep_n hstep_inv

lemma circuitFun_circuitMap (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n (circuitMap n σ C) x = circuitFun n C (x ∘ σ) := by
  unfold circuitFun Circuit.eval Circuit.wires circuitMap
  have hbase : ∀ u : ℕ,
      (List.ofFn x).getD (wireMap n σ u) false = (List.ofFn (x ∘ σ)).getD u false := by
    intro u
    by_cases hu : u < n
    · have hw : wireMap n σ u = (σ ⟨u, hu⟩).val := by simp [wireMap, hu]
      rw [hw]
      simp [List.getD_eq_getElem?_getD, hu, (σ ⟨u, hu⟩).isLt]
    · have hw : wireMap n σ u = u := wireMap_ge n σ (Nat.le_of_not_lt hu)
      rw [hw]
      rw [getD_ge_len (List.ofFn x) (by simp; omega),
        getD_ge_len (List.ofFn (x ∘ σ)) (by simp; omega)]
  have hfold := (foldl_wireMap n σ C.gates (List.ofFn (x ∘ σ)) (List.ofFn x)
    (by simp) (by simp) hbase).2 C.output
  exact hfold

lemma fanInTwo_circuitMap (n : ℕ) (σ : Equiv.Perm (Fin n)) {C : Circuit} (hC : FanInTwo C) :
    FanInTwo (circuitMap n σ C) := by
  intro g hg
  simp only [circuitMap, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨hop, hlen⟩ := hC g0 hg0
  exact ⟨hop, by simp [gateMap, hlen]⟩

lemma size_circuitMap (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) :
    (circuitMap n σ C).size = C.size := by
  simp [Circuit.size, circuitMap]

lemma isMinimal_circuitMap (n : ℕ) (σ : Equiv.Perm (Fin n)) {C : Circuit}
    (hmin : IsMinimalCircuit n C) :
    IsMinimalCircuit n (circuitMap n σ C) := by
  refine ⟨fanInTwo_circuitMap n σ hmin.1, ?_⟩
  intro D hD hfun
  let D' := circuitMap n σ.symm D
  have hD' : FanInTwo D' := fanInTwo_circuitMap n σ.symm hD
  have hfun' : circuitFun n D' = circuitFun n C := by
    funext x
    calc
      circuitFun n D' x = circuitFun n D (x ∘ σ.symm) := circuitFun_circuitMap n σ.symm D x
      _ = circuitFun n (circuitMap n σ C) (x ∘ σ.symm) := congrFun hfun (x ∘ σ.symm)
      _ = circuitFun n C ((x ∘ σ.symm) ∘ σ) := circuitFun_circuitMap n σ C (x ∘ σ.symm)
      _ = circuitFun n C x := by
        congr 1
        funext i
        simp
  have hle : C.size ≤ D'.size := hmin.2 D' hD' hfun'
  rw [size_circuitMap] at hle ⊢
  exact hle

end PEqualNP.Outside.L_meta_4203

theorem PEqualNP.Outside.L_meta_4203 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Equiv.Perm (Fin x1)),   ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin x2.size ≃ Fin x4.size),     x4.size = x2.size ∧       (PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4) ∧         (∀ (x6 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x4 x6 = PEqualNP.MetaComplexity.circuitFun x1 x2 (x6 ∘ ⇑x3)) ∧           ∀ (x6 : Fin x2.size),             have x7 : PEqualNP.CircuitLowerBounds.Gate := x2.gates.get x6;             have x8 : PEqualNP.CircuitLowerBounds.Gate := x4.gates.get (x5 x6);             x8.op = x7.op ∧ x8.inputs.length = x7.inputs.length ∧ (x7.inputs.Nodup → x8.inputs.Nodup) ∧ ((∀ x9 ∈ x7.inputs, x9 < x1 + ↑x6) → ∀ x10 ∈ x8.inputs, x10 < x1 + ↑(x5 x6)) ∧ ∀ (x9 : Fin x1), ↑(x3 x9) ∈ x8.inputs ↔ ↑x9 ∈ x7.inputs := by
  intro n C σ
  let C' := PEqualNP.Outside.L_meta_4203.circuitMap n σ C
  have hsz : C'.size = C.size := PEqualNP.Outside.L_meta_4203.size_circuitMap n σ C
  refine ⟨C', finCongr hsz.symm, hsz, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_4203.isMinimal_circuitMap n σ
  · exact PEqualNP.Outside.L_meta_4203.circuitFun_circuitMap n σ C
  · intro i
    have hget : C'.gates.get (finCongr hsz.symm i) =
        PEqualNP.Outside.L_meta_4203.gateMap n σ (C.gates.get i) := by
      change (C.gates.map (PEqualNP.Outside.L_meta_4203.gateMap n σ))[i.val]'(by
        rw [List.length_map]; exact i.isLt) =
        PEqualNP.Outside.L_meta_4203.gateMap n σ (C.gates[i.val]'i.isLt)
      exact List.getElem_map (PEqualNP.Outside.L_meta_4203.gateMap n σ)
    dsimp only
    rw [hget]
    refine ⟨rfl, by simp [PEqualNP.Outside.L_meta_4203.gateMap], ?_, ?_, ?_⟩
    · intro hnd
      exact hnd.map (PEqualNP.Outside.L_meta_4203.wireMap_inj n σ)
    · intro hlt w hw
      simp only [PEqualNP.Outside.L_meta_4203.gateMap, List.mem_map] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      have hval : (finCongr hsz.symm i).val = i.val := rfl
      rw [hval]
      exact PEqualNP.Outside.L_meta_4203.wireMap_lt n σ (hlt u hu)
    · intro j
      simp only [PEqualNP.Outside.L_meta_4203.gateMap, List.mem_map]
      constructor
      · rintro ⟨u, hu, heq⟩
        have h1 : PEqualNP.Outside.L_meta_4203.wireMap n σ u =
            PEqualNP.Outside.L_meta_4203.wireMap n σ j.val := by
          rw [PEqualNP.Outside.L_meta_4203.wireMap_fin]
          exact heq
        have h2 : u = j.val := PEqualNP.Outside.L_meta_4203.wireMap_inj n σ h1
        rw [← h2]
        exact hu
      · intro hj
        exact ⟨j.val, hj, PEqualNP.Outside.L_meta_4203.wireMap_fin n σ j⟩
