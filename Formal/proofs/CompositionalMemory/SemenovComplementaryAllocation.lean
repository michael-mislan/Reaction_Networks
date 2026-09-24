import proofs.CompositionalMemory.BinomialAllocationReflection
import proofs.CompositionalMemory.SemenovAllocationSupport

namespace CompositionalMemory.Semenov
open MeasureTheory ProbabilityTheory

abbrev JointRawAllocation := Fin 8 → ℕ × (ℕ × ℕ)

noncomputable def jointRefillMeasure (n : ℕ) (t : NNReal) : Measure (ℕ × (ℕ × ℕ)) :=
  (fairAllocationMeasure n).prod ((poissonMeasure t).prod (poissonMeasure t))

instance jointRefillMeasure_probability (n : ℕ) (t : NNReal) : IsProbabilityMeasure (jointRefillMeasure n t) := by
  unfold jointRefillMeasure
  infer_instance

noncomputable def complementaryAllocationLaw (n : Fin 8 → ℕ) (t : Fin 8 → NNReal) : Measure JointRawAllocation :=
  Measure.pi (fun j => jointRefillMeasure (n j) (t j))

instance complementaryAllocationLaw_probability (n : Fin 8 → ℕ) (t : Fin 8 → NNReal) :
    IsProbabilityMeasure (complementaryAllocationLaw n t) := by
  unfold complementaryAllocationLaw
  infer_instance

def daughterAllocationA (z : JointRawAllocation) : RawAllocation := fun j => ((z j).1,(z j).2.1)
def daughterAllocationB (n : Fin 8 → ℕ) (z : JointRawAllocation) : RawAllocation :=
  fun j => (n j-(z j).1,(z j).2.2)

theorem joint_refill_marginal_A (n : ℕ) (t : NNReal) :
    MeasurePreserving (fun z : ℕ × (ℕ × ℕ) => (z.1,z.2.1))
      (jointRefillMeasure n t) (refillAllocationMeasure n t) := by
  have hi : MeasurePreserving (id : ℕ → ℕ) (fairAllocationMeasure n) (fairAllocationMeasure n) :=
    ⟨measurable_id,Measure.map_id⟩
  exact hi.prod (measurePreserving_fst (μ := poissonMeasure t) (ν := poissonMeasure t))

theorem joint_refill_marginal_B (n : ℕ) (t : NNReal) :
    MeasurePreserving (fun z : ℕ × (ℕ × ℕ) => (n-z.1,z.2.2))
      (jointRefillMeasure n t) (refillAllocationMeasure n t) := by
  exact (fair_allocation_reflection n).prod
    (measurePreserving_snd (μ := poissonMeasure t) (ν := poissonMeasure t))

theorem complementary_marginal_A (n : Fin 8 → ℕ) (t : Fin 8 → NNReal) :
    MeasurePreserving daughterAllocationA (complementaryAllocationLaw n t) (allocationLaw n t) :=
  measurePreserving_pi _ _ (fun j => joint_refill_marginal_A (n j) (t j))

theorem complementary_marginal_B (n : Fin 8 → ℕ) (t : Fin 8 → NNReal) :
    MeasurePreserving (daughterAllocationB n) (complementaryAllocationLaw n t) (allocationLaw n t) :=
  measurePreserving_pi _ _ (fun j => joint_refill_marginal_B (n j) (t j))

theorem complementary_integral_A (n : Fin 8 → ℕ) (t : Fin 8 → NNReal) (f : RawAllocation → ℝ) :
    (∫ z,f (daughterAllocationA z) ∂complementaryAllocationLaw n t)=∫ z,f z ∂allocationLaw n t := by
  have hm := complementary_marginal_A n t
  rw [← hm.map_eq]
  exact (integral_map hm.aemeasurable (measurable_of_countable f).aestronglyMeasurable).symm

theorem complementary_integral_B (n : Fin 8 → ℕ) (t : Fin 8 → NNReal) (f : RawAllocation → ℝ) :
    (∫ z,f (daughterAllocationB n z) ∂complementaryAllocationLaw n t)=∫ z,f z ∂allocationLaw n t := by
  have hm := complementary_marginal_B n t
  rw [← hm.map_eq]
  exact (integral_map hm.aemeasurable (measurable_of_countable f).aestronglyMeasurable).symm

theorem complementary_partition_conserved (n : Fin 8 → ℕ) (t : Fin 8 → NNReal) :
    ∀ᵐ z ∂complementaryAllocationLaw n t,∀ j,
      (daughterAllocationA z j).1+(daughterAllocationB n z j).1=n j := by
  have hh := (complementary_marginal_A n t).quasiMeasurePreserving.ae (allocation_partition_support n t)
  filter_upwards [hh] with z hz
  intro j
  have hj := hz j
  change (z j).1 ≤ n j at hj
  change (z j).1+(n j-(z j).1)=n j
  omega

end CompositionalMemory.Semenov
