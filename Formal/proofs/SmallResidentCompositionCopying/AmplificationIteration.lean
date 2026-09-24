import proofs.SmallResidentCompositionCopying.AmplificationProtocol
import proofs.CompositionalMemory.FiniteLineageKernel

namespace SmallResidentCompositionCopying.Amplification
open Classical FiniteCopy CompositionalMemory HeritableCompositions
open scoped ENNReal
noncomputable section
set_option profiler true
set_option maxHeartbeats 100000

abbrev NewbornCounts := Fin 19 × Fin 19
def embedNewborn (z : NewbornCounts) : Counts :=
  (⟨z.1.val,by omega⟩,⟨z.2.val,by omega⟩)

def completed : Option (Counts × Fin quota) → ℝ
  | none => 0
  | some (z,_) => if z.1.val=19 ∧ z.2.val=19 then 1 else 0

def completionProbability (word : Word) (z : Counts) : ℝ :=
  finiteTimeExpectation (chemicalCycle word) 20 completed (cycleStart z)

theorem completion_nonneg (word : Word) (z : Counts) : 0 ≤ completionProbability word z := by
  apply (finite_time_bounds (chemicalCycle word) 20 completed ?_ (cycleStart z)).1
  intro s
  cases s with
  | none => norm_num [completed]
  | some s => dsimp [completed]; split_ifs <;> norm_num

theorem return_factorization (word : Word) (z : Counts) :
    actualJointReturn word z = completionProbability word z * partitionSuccess := by
  have hf : actualTerminal = fun s => completed s*partitionSuccess := by
    funext s
    cases s <;> simp [actualTerminal,completed,exact_partition]
  simp only [actualJointReturn,completionProbability,hf,finiteTimeExpectation,
    Matrix.mulVec,dotProduct]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

def offspringWeight (z : NewbornCounts) : ℝ :=
  allocationWeight (z.1.val+1) (z.2.val+1)

theorem offspring_sum : (∑ z : NewbornCounts, offspringWeight z)=partitionSuccess := by
  have h : (∑ a : Fin 19, fairBinomialWeight 20 (a.val+1))=(1048574:ℝ)/1048576 := by
    have ht := fair_binomial_sum 20
    rw [Finset.sum_range_succ'] at ht
    rw [Finset.sum_range_succ] at ht
    have hzero : fairBinomialWeight 20 0=(1:ℝ)/1048576 := by norm_num [fairBinomialWeight]
    have hlast : fairBinomialWeight 20 20=(1:ℝ)/1048576 := by norm_num [fairBinomialWeight]
    change (∑ a ∈ Finset.range 19, fairBinomialWeight 20 (a+1)) +
      fairBinomialWeight 20 20 + fairBinomialWeight 20 0=1 at ht
    rw [hzero,hlast] at ht
    rw [Fin.sum_univ_eq_sum_range (fun a => fairBinomialWeight 20 (a+1)) 19]
    linarith only [ht]
  simp only [offspringWeight,allocationWeight,Fintype.sum_prod_type,← Finset.mul_sum]
  rw [h,← Finset.sum_mul,h]
  exact (pow_two _).symm

def lineageWeight (word : Word) (a b : NewbornCounts) : ℝ≥0∞ :=
  ENNReal.ofReal (completionProbability word (embedNewborn a) * offspringWeight b)

theorem lineage_sum (word : Word) (a : NewbornCounts) :
    (∑ b, lineageWeight word a b)=ENNReal.ofReal (actualJointReturn word (embedNewborn a)) := by
  unfold lineageWeight
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [← Finset.mul_sum,offspring_sum,← return_factorization]
  · intro b _
    exact mul_nonneg (completion_nonneg word _) (mul_nonneg
      (fairBinomialWeight_nonneg _ _) (fairBinomialWeight_nonneg _ _))

def lineage (word : Word) : FiniteLineageKernel NewbornCounts where
  weight := lineageWeight word
  total_le_one a := by
    rw [lineage_sum]
    exact ENNReal.ofReal_le_one.mpr (actual_probability_bounds word _).2

/-- Both daughters are inspected and daughterA continues, with fresh external
resources, clock and quota at each restart. No inter-generation independence
is assumed beyond using the same state-dependent cycle kernel. -/
theorem repeated_copying (word : Word) (n : ℕ) (a : NewbornCounts) :
    (99/100:ℝ≥0∞)^n ≤ (lineage word).survival n a := by
  apply FiniteLineageKernel.survival_lower
  intro z
  change (99/100:ℝ≥0∞) ≤ ∑ b, lineageWeight word z b
  rw [lineage_sum]
  have h := ENNReal.ofReal_le_ofReal (actual_joint_return word (embedNewborn z))
  norm_num [ENNReal.ofReal_div_of_pos] at h
  exact h

end
end SmallResidentCompositionCopying.Amplification
