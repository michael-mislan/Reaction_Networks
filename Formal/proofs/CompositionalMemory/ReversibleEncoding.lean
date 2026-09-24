import proofs.CompositionalMemory.ReversibleOffspringAllocation

namespace CompositionalMemory
open ControlledRows

def reversibleEncodeModule (col : Fin 2) : Fin 849 × Fin 213 :=
  if col=0 then (⟨53,by norm_num⟩,0) else (⟨530,by norm_num⟩,⟨53,by norm_num⟩)

theorem reversibleEncodeModule_newborn (col : Fin 2) :
    newborn 53 col.val (reversibleEncodeModule col).1.val (reversibleEncodeModule col).2.val := by
  fin_cases col <;> norm_num [reversibleEncodeModule,newborn]

def reversibleEncodeWord (word : Fin 2 → Fin 2) : ReversibleWordNewborn word :=
  ⟨(reversibleEncodeModule (word 0),reversibleEncodeModule (word 1)),
    reversibleEncodeModule_newborn (word 0),reversibleEncodeModule_newborn (word 1)⟩

def reversibleDecodeModule (x : Nat) : Fin 2 := if 212 < x then 1 else 0

theorem reversibleDecodeModule_correct (col : Fin 2) (x y : Nat) (hb : newborn 53 col.val x y) :
    reversibleDecodeModule x=col := by
  fin_cases col
  · have hx : x ≤ 106 := by norm_num [newborn] at hb; omega
    simp [reversibleDecodeModule,show ¬212 < x by omega]
  · have hx : 371 ≤ x := by norm_num [newborn] at hb; omega
    simp [reversibleDecodeModule,show 212 < x by omega]

/-- All four words have explicit admitted newborns and one fixed blind decoder. -/
theorem reversible_encoding_nonvacuous (word : Fin 2 → Fin 2) :
    ∃ b : ReversibleWordNewborn word,
      reversibleDecodeModule b.val.1.1.val=word 0 ∧ reversibleDecodeModule b.val.2.1.val=word 1 := by
  refine ⟨reversibleEncodeWord word,?_,?_⟩
  · exact reversibleDecodeModule_correct _ _ _ (reversibleEncodeWord word).property.1
  · exact reversibleDecodeModule_correct _ _ _ (reversibleEncodeWord word).property.2

end CompositionalMemory
