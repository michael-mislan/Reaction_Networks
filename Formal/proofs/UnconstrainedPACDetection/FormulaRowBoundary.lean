import proofs.UnconstrainedPACDetection.FormulaAllTails

namespace UnconstrainedPACDetection.FormulaRowBoundary
open Complexity.SAT DirectedLinkageSource
open FormulaWiring (levels varCount)

theorem labels_length (φ : CNF) : (FormulaIndexedGraph.labels φ).length = FormulaClauseCursor.base φ+φ.length+1 := by
  have h := congrArg List.length (FormulaClauseCursor.labels φ)
  simpa only [List.length_append,FormulaClauseCursor.initialVertices_length,List.length_map,List.length_finRange,Nat.add_assoc] using h

theorem clause_index (φ : CNF) (c : Fin (φ.length+1)) :
    ((FormulaIndexedGraph.vertexEquiv φ).symm (.inr (.clause c))).val = FormulaClauseCursor.base φ+c.val := by
  have hb : FormulaClauseCursor.base φ+c.val < (FormulaIndexedGraph.labels φ).length := by
    rw [labels_length]; have h := c.isLt; omega
  have he : FormulaIndexedGraph.vertexEquiv φ ⟨FormulaClauseCursor.base φ+c.val,hb⟩ = .inr (.clause c) := by
    change (FormulaIndexedGraph.labels φ)[FormulaClauseCursor.base φ+c.val] = _
    simp only [FormulaClauseCursor.labels]
    rw [List.getElem_append_right (by rw [FormulaClauseCursor.initialVertices_length]; omega)]
    simp [FormulaClauseCursor.initialVertices_length]
  exact congrArg Fin.val ((FormulaIndexedGraph.vertexEquiv φ).symm_apply_eq.mpr he.symm)

def boundary (φ : CNF) : Bool ⊕ Bool → Nat
  | .inl false => 1
  | .inl true => 20*(levels φ-1)
  | .inr false => FormulaClauseCursor.base φ+φ.length
  | .inr true => 4

theorem terminal_index (φ : CNF) (t : Bool ⊕ Bool) :
    (FormulaIndexedGraph.terminals φ t).val = boundary φ t := by
  cases t with
  | inl b =>
    cases b with
    | false =>
      have h := FormulaSwitchCursor.index φ ⟨0,FormulaWiring.levels_pos φ⟩ 1
      simpa only [FormulaIndexedGraph.terminals,PACFormulaReduction.terminals,PACFormulaReduction.terminal,
        FormulaWiring.sourceP,boundary,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Nat.mul_zero,Nat.zero_add] using h
    | true =>
      have h := FormulaSwitchCursor.index φ ⟨levels φ-1,by have h := FormulaWiring.levels_pos φ; omega⟩ 0
      simpa only [FormulaIndexedGraph.terminals,PACFormulaReduction.terminals,PACFormulaReduction.terminal,
        FormulaWiring.sourceQ,boundary,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Nat.add_zero] using h
  | inr b =>
    cases b with
    | false =>
      have h := clause_index φ (Fin.last φ.length)
      simpa only [FormulaIndexedGraph.terminals,PACFormulaReduction.terminals,PACFormulaReduction.terminal,
        FormulaWiring.sinkP,boundary,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Fin.val_last] using h
    | true =>
      have h := FormulaSwitchCursor.index φ ⟨0,FormulaWiring.levels_pos φ⟩ 4
      simpa only [FormulaIndexedGraph.terminals,PACFormulaReduction.terminals,PACFormulaReduction.terminal,
        FormulaWiring.sinkQ,boundary,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Nat.mul_zero,Nat.zero_add] using h

theorem internal_iff (φ : CNF) (k : Fin (FormulaIndexedGraph.labels φ).length) :
    k ∉ Set.range (FormulaIndexedGraph.terminals φ) ↔
      k.val ≠ 1 ∧ k.val ≠ 4 ∧ k.val ≠ 20*(levels φ-1) ∧ k.val ≠ FormulaClauseCursor.base φ+φ.length := by
  have he (t : Bool ⊕ Bool) : FormulaIndexedGraph.terminals φ t = k ↔ boundary φ t = k.val := by
    rw [Fin.ext_iff,terminal_index]
  simp only [Set.mem_range,not_exists,he]
  constructor
  · intro h
    exact ⟨Ne.symm (h (.inl false)),Ne.symm (h (.inr true)),Ne.symm (h (.inl true)),Ne.symm (h (.inr false))⟩
  · rintro ⟨h1,h4,hq,hp⟩ t
    cases t with
    | inl b => cases b <;> first | exact Ne.symm h1 | exact Ne.symm hq
    | inr b => cases b <;> first | exact Ne.symm hp | exact Ne.symm h4

end UnconstrainedPACDetection.FormulaRowBoundary
