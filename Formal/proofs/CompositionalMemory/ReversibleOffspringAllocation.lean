import proofs.CompositionalMemory.ReversibleBoundedPartition
import proofs.CompositionalMemory.ReversibleFirstDivision

namespace CompositionalMemory
open Classical ControlledRows
open scoped ENNReal
noncomputable section

abbrev ReversibleNewbornPair := (Fin 849 × Fin 213) × (Fin 849 × Fin 213)

def reversiblePairNewborn (word : Fin 2 → Fin 2) (b : ReversibleNewbornPair) : Prop :=
  newborn 53 (word 0).val b.1.1.val b.1.2.val ∧ newborn 53 (word 1).val b.2.1.val b.2.2.val

instance (word : Fin 2 → Fin 2) (b : ReversibleNewbornPair) : Decidable (reversiblePairNewborn word b) := by
  unfold reversiblePairNewborn
  infer_instance

abbrev ReversibleWordNewborn (word : Fin 2 → Fin 2) := {b : ReversibleNewbornPair // reversiblePairNewborn word b}

def reversiblePairArray (b : ReversibleNewbornPair) : Fin 2 → Fin 849 × Fin 213 := ![b.1,b.2]

theorem reversiblePairArray_newborn (word : Fin 2 → Fin 2) (b : ReversibleWordNewborn word) :
    ∀ k, newborn 53 (word k).val (reversiblePairArray b.val k).1.val (reversiblePairArray b.val k).2.val := by
  intro k
  fin_cases k
  · exact b.property.1
  · exact b.property.2

def reversibleOffspringReal (word : Fin 2 → Fin 2) (s : ReversibleBudgetState 53) (b : ReversibleNewbornPair) : ℝ :=
  if controlledBothNewborn 53 (word 0).val ((reversibleBudgetCounts 53 s).2 0).1.toNat ((reversibleBudgetCounts 53 s).2 0).2.toNat b.1.1.val b.1.2.val ∧
     controlledBothNewborn 53 (word 1).val ((reversibleBudgetCounts 53 s).2 1).1.toNat ((reversibleBudgetCounts 53 s).2 1).2.toNat b.2.1.val b.2.2.val then
    coupledPartitionWeight ((reversibleBudgetCounts 53 s).2 0).1.toNat ((reversibleBudgetCounts 53 s).2 0).2.toNat ((reversibleBudgetCounts 53 s).2 1).1.toNat ((reversibleBudgetCounts 53 s).2 1).2.toNat
      b.1.1.val b.1.2.val b.2.1.val b.2.2.val else 0

theorem reversibleOffspringReal_nonneg (word : Fin 2 → Fin 2) (s : ReversibleBudgetState 53) (b : ReversibleNewbornPair) :
    0 ≤ reversibleOffspringReal word s b := by
  unfold reversibleOffspringReal
  split_ifs
  · exact coupledPartitionWeight_nonneg _ _ _ _ _ _ _ _
  · exact le_rfl

theorem reversibleOffspringReal_outside (word : Fin 2 → Fin 2) (s : ReversibleBudgetState 53)
    (b : ReversibleNewbornPair) (hb : ¬reversiblePairNewborn word b) : reversibleOffspringReal word s b=0 := by
  have hh : ¬(controlledBothNewborn 53 (word 0).val ((reversibleBudgetCounts 53 s).2 0).1.toNat ((reversibleBudgetCounts 53 s).2 0).2.toNat b.1.1.val b.1.2.val ∧
      controlledBothNewborn 53 (word 1).val ((reversibleBudgetCounts 53 s).2 1).1.toNat ((reversibleBudgetCounts 53 s).2 1).2.toNat b.2.1.val b.2.2.val) := by
    intro h
    exact hb ⟨h.1.1,h.2.1⟩
  simp [reversibleOffspringReal,hh]

theorem reversibleOffspringReal_sum (word : Fin 2 → Fin 2) (s : ReversibleBudgetState 53) :
    (∑ b : ReversibleNewbornPair,reversibleOffspringReal word s b)=
      terminalReward 53 ((reversibleBudgetCounts 53 s).2 0).1.toNat ((reversibleBudgetCounts 53 s).2 0).2.toNat (word 0).val*
      terminalReward 53 ((reversibleBudgetCounts 53 s).2 1).1.toNat ((reversibleBudgetCounts 53 s).2 1).2.toNat (word 1).val := by
  have he (a0 : Fin 849) (b0 : Fin 213) (a1 : Fin 849) (b1 : Fin 213) :
      reversibleOffspringReal word s ((a0,b0),(a1,b1))=
      (if controlledBothNewborn 53 (word 0).val ((reversibleBudgetCounts 53 s).2 0).1.toNat ((reversibleBudgetCounts 53 s).2 0).2.toNat a0.val b0.val
        then widePartitionWeight ((reversibleBudgetCounts 53 s).2 0).1.toNat ((reversibleBudgetCounts 53 s).2 0).2.toNat a0.val b0.val else 0)*
      (if controlledBothNewborn 53 (word 1).val ((reversibleBudgetCounts 53 s).2 1).1.toNat ((reversibleBudgetCounts 53 s).2 1).2.toNat a1.val b1.val
        then widePartitionWeight ((reversibleBudgetCounts 53 s).2 1).1.toNat ((reversibleBudgetCounts 53 s).2 1).2.toNat a1.val b1.val else 0) := by
    unfold reversibleOffspringReal coupledPartitionWeight
    split_ifs <;> simp_all
  simp only [Fintype.sum_prod_type]
  simp_rw [he]
  simp only [← Finset.mul_sum,bounded_reversible_partition,← Finset.sum_mul]

def reversibleOffspringWeight (word : Fin 2 → Fin 2) (s : ReversibleBudgetState 53)
    (b : ReversibleWordNewborn word) : ℝ≥0∞ := ENNReal.ofReal (reversibleOffspringReal word s b.val)

theorem reversibleOffspringWeight_sum (word : Fin 2 → Fin 2) (s : ReversibleBudgetState 53) :
    (∑ b : ReversibleWordNewborn word,reversibleOffspringWeight word s b)=reversibleParentReward 53 word s := by
  have hr : (∑ b : ReversibleWordNewborn word,reversibleOffspringReal word s b.val)=
      ∑ b : ReversibleNewbornPair,reversibleOffspringReal word s b := by
    rw [← Finset.sum_subtype (p := reversiblePairNewborn word) (Finset.univ.filter (reversiblePairNewborn word)) (by simp)
      (reversibleOffspringReal word s)]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b _ hb
    exact reversibleOffspringReal_outside word s b (by simpa using hb)
  unfold reversibleOffspringWeight
  rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => reversibleOffspringReal_nonneg word s b.val),hr,
    reversibleOffspringReal_sum]
  rfl

end
end CompositionalMemory
