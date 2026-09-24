import proofs.ProductiveMemory.ExtractionReadout
import proofs.ProductiveMemory.ExtractionHistory

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
noncomputable section
set_option Elab.async false

theorem z_inventory_of_cell_bounds (cs : List TaggedCell)
    (h : ∀ c ∈ cs, c.compartment.1 2 ≤ 3*c.compartment.2) : zInventory cs ≤ 3*membrane cs := by
  induction cs with
  | nil => simp [zInventory,membrane]
  | cons c cs ih =>
    have hc := h c (by simp)
    have ht := ih (fun d hd => h d (by simp [hd]))
    simp only [zInventory,List.map_cons,List.sum_cons,membrane_cons]
    change _+(zInventory cs) ≤ _
    omega

theorem productive_ready_z_stock (N M : ℕ) (hN : 0 < N) (rho zL zH : ℝ)
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (s : ProductiveReady N M rho zL zH) : zInventory s.val.population.live ≤ 3*membrane s.val.population.live := by
  apply z_inventory_of_cell_bounds
  intro c hc
  have hm : (0:ℝ)<c.compartment.2 := by
    exact_mod_cast hN.trans_le ((productiveReady_ready N M rho zL zH s).2.2.2.1 c hc).1
  have hr := productive_ready_readout N M rho zL zH hzL hzH s c hc
  have hz : concentration c.compartment.2 c.compartment.1 2 ≤ 3 := by
    cases hh : c.high <;> simp only [hh,Bool.false_eq_true,ite_false,ite_true] at hr
    · exact hr.2.trans (by norm_num)
    · exact hr.2
  have hb := (div_le_iff₀ hm).mp hz
  exact_mod_cast hb

/-- Any actual history attaining the proved batch threshold has positive net internal z formation.
Recovery exports and discarded molecules are included in the account, not silently dropped. -/
theorem productive_export_net_production (N M : ℕ) (hN : 0 < N) (rho zL zH : ℝ)
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (initial : ProductiveReady N M rho zL zH) (s : ProductiveState) (P : ℝ) (G D : ℕ)
    (hist : ProductiveHistory N initial.val s P G D)
    (hout : 5*membrane initial.val.population.live < s.collected) : 0 < P := by
  apply productive_positive_net_formation N initial.val s P G D hist
    (productiveReady_ready N M rho zL zH initial).2.2.2.2.2
  have hz := productive_ready_z_stock N M hN rho zL zH hzL hzH initial
  omega

end
end ProductiveMemory
