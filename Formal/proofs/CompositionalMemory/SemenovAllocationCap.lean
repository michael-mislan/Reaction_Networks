import proofs.CompositionalMemory.SemenovAllocationSupport
import proofs.CompositionalMemory.SemenovAllocationEnergy

namespace CompositionalMemory.Semenov
open MeasureTheory ProbabilityTheory

theorem smooth_cap_monotone : Monotone smoothQuadraticCap := by
  intro a b hab
  by_cases hb : b ≤ 1
  · have ha := hab.trans hb
    simp only [smoothQuadraticCap,if_pos ha,if_pos hb]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ 2-a-b by linarith only [ha,hb])]
  · simp only [smoothQuadraticCap,if_neg hb]
    exact smoothQuadraticCap_le_one a

theorem cap_integrable_countable {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (E : α → ℝ) (hE : ∀ z,0 ≤ E z) : Integrable (fun z => smoothQuadraticCap (E z)) μ := by
  apply (integrable_const (1 : ℝ)).mono_nonneg
    (measurable_of_countable (fun z => smoothQuadraticCap (E z))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z => smoothQuadraticCap_nonneg _ (hE z))
  · exact Filter.Eventually.of_forall (fun z => smoothQuadraticCap_le_one _)

theorem allocation_combined_cap_bound (n : Fin 8 → ℕ) (t : Fin 8 → NNReal)
    (B K : ℕ) (hK : 0 < K) (hbudget : (∑ j,n j)+K ≤ B)
    (E : (Fin 8 → ℕ) → ℝ) (hE : ∀ n,0 ≤ E n) (rate : ℝ)
    (hm : (∑ j,(t j : ℝ)) ≤ (K : ℝ)/2) :
    (∫ z,smoothQuadraticCap (reactorCombinedEnergy E (∑ j,(t j : ℝ)) rate 0
        (encodeReactor B K (refilledCounts z) (allocationFeedCount z))) ∂allocationLaw n t) ≤
      (∫ z,smoothQuadraticCap (E (refilledCounts z)) ∂allocationLaw n t)+
        64*(∑ j,(t j : ℝ))/(K : ℝ)^2 := by
  have hpoint := allocation_combined_energy_comparison n t B K hK hbudget E hE rate hm
  have hi := initial_inventory_bound n t (K : ℝ) rate
  have hleft := cap_integrable_countable (allocationLaw n t)
    (fun z => reactorCombinedEnergy E (∑ j,(t j : ℝ)) rate 0
      (encodeReactor B K (refilledCounts z) (allocationFeedCount z)))
    (fun z => reactor_combined_energy_nonneg E hE _ _ _ _)
  have he := cap_integrable_countable (allocationLaw n t) (fun z => E (refilledCounts z)) (fun z => hE _)
  have hbound := integral_mono_ae hleft (he.add (hi.1.const_mul 2)) (by
    filter_upwards [hpoint] with z hz
    exact (smooth_cap_monotone hz).trans (smoothQuadraticCap_add_cost _ _ (hE _)
      (centeredInventory_nonneg _ _ _ _ _)))
  simp only [Pi.add_apply] at hbound
  rw [integral_add he (hi.1.const_mul 2),integral_const_mul] at hbound
  have hh : 2*(∫ z,centeredInventory K (∑ j,(t j : ℝ)) rate 0 (allocationFeedCount z) ∂allocationLaw n t) ≤
      64*(∑ j,(t j : ℝ))/(K : ℝ)^2 := by
    calc
      _ ≤ 2*(32*(∑ j,(t j : ℝ))/(K : ℝ)^2) := mul_le_mul_of_nonneg_left hi.2 (by norm_num)
      _ = _ := by ring
  exact hbound.trans (add_le_add le_rfl hh)

end CompositionalMemory.Semenov
