import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24889.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_24889.Helpers

theorem PEqualNP.Outside.L_meta_24889 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2215351 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24889.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24889.Helpers.witness]
