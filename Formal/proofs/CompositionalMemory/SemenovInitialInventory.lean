import proofs.CompositionalMemory.SemenovAllocationLaw
import proofs.CompositionalMemory.CenteredInventory

namespace CompositionalMemory.Semenov
open MeasureTheory ProbabilityTheory FiniteCopy

def allocationFeedCount (z : RawAllocation) : ℕ := ∑ j,(z j).2

noncomputable def feedNoise (t : Fin 8 → NNReal) (j : Fin 8) (z : RawAllocation) : ℝ :=
  ((z j).2 : ℝ)-t j

theorem feed_noise_second (n : Fin 8 → ℕ) (t : Fin 8 → NNReal) (j : Fin 8) :
    Integrable (fun z => feedNoise t j z^2) (allocationLaw n t) ∧
      (∫ z,feedNoise t j z^2 ∂allocationLaw n t)=(t j : ℝ) := by
  have hi := poisson_integrable_of_hasSum (t j) _ _ (poisson_centered_second (t j))
  have hp : Integrable (fun z : ℕ × ℕ => ((z.2 : ℝ)-t j)^2)
      (refillAllocationMeasure (n j) (t j)) := hi.comp_snd (fairAllocationMeasure (n j))
  constructor
  · exact integrable_comp_eval (μ := fun i => refillAllocationMeasure (n i) (t i)) (i := j) hp
  · rw [show (∫ z,feedNoise t j z^2 ∂allocationLaw n t)=
        ∫ z : ℕ × ℕ,((z.2 : ℝ)-t j)^2 ∂refillAllocationMeasure (n j) (t j) from
      integral_comp_eval (μ := fun i => refillAllocationMeasure (n i) (t i)) (i := j) hp.aestronglyMeasurable]
    have hh := integral_prod_mul (μ := fairAllocationMeasure (n j)) (ν := poissonMeasure (t j))
      (fun _ : ℕ => (1 : ℝ)) (fun k : ℕ => ((k : ℝ)-t j)^2)
    simpa only [one_mul,integral_const,probReal_univ,one_smul,
      (poisson_actual_centered_moments (t j)).2.1] using hh

theorem initial_inventory_bound (n : Fin 8 → ℕ) (t : Fin 8 → NNReal) (K rate : ℝ) :
    Integrable (fun z => centeredInventory K (∑ j,(t j : ℝ)) rate 0 (allocationFeedCount z))
      (allocationLaw n t) ∧
    (∫ z,centeredInventory K (∑ j,(t j : ℝ)) rate 0 (allocationFeedCount z) ∂allocationLaw n t) ≤
      32*(∑ j,(t j : ℝ))/K^2 := by
  let C : RawAllocation → ℝ := fun z => ((allocationFeedCount z : ℝ)-∑ j,(t j : ℝ))^2
  have he (z : RawAllocation) : (allocationFeedCount z : ℝ)-(∑ j,(t j : ℝ))=∑ j,feedNoise t j z := by
    simp only [allocationFeedCount,Nat.cast_sum,feedNoise,Finset.sum_sub_distrib]
  have hb (z : RawAllocation) : 0 ≤ C z ∧ C z ≤ 8*∑ j,feedNoise t j z^2 := by
    refine ⟨sq_nonneg _,?_⟩
    dsimp only [C]
    rw [he]
    have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 8 => (1 : ℝ)) (fun j => feedNoise t j z)
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_ofNat] using hh
  have hi := (integrable_finsetSum Finset.univ (fun j _ => (feed_noise_second n t j).1)).const_mul (8 : ℝ)
  have hic : Integrable C (allocationLaw n t) := hi.mono_nonneg
    (measurable_of_countable C).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => (hb z).1)) (Filter.Eventually.of_forall (fun z => (hb z).2))
  have hm : (∫ z,C z ∂allocationLaw n t) ≤ 8*∑ j,(t j : ℝ) := by
    have hh := integral_mono hic hi (fun z => (hb z).2)
    rw [integral_const_mul,integral_finsetSum _ (fun j _ => (feed_noise_second n t j).1)] at hh
    simpa only [(feed_noise_second n t _).2] using hh
  have hid (z : RawAllocation) : centeredInventory K (∑ j,(t j : ℝ)) rate 0 (allocationFeedCount z)=(4/K^2)*C z := by
    dsimp [centeredInventory,C]
    ring
  simp_rw [hid]
  refine ⟨hic.const_mul _,?_⟩
  rw [integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 4/K^2)
  convert hh using 1
  ring

end CompositionalMemory.Semenov
