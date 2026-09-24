import proofs.CompositionalMemory.GenericGlobalReactions
import proofs.CompositionalMemory.GenericFactorialSlots

namespace CompositionalMemory

theorem general_resident_observable_local {k d : ℕ} (s : GeneralCountState k d)
    (i j : Fin k) (consume produce : Fin d → ℕ) (c : ℝ) (W : (Fin d → ℝ) → ℝ) :
    (((s.2:ℝ)/k)*countReactionDensity c ((s.2:ℝ)/k) consume (s.1 j))*
      (W (generalConcentration (generalResidentNext s j consume produce) i)-W (generalConcentration s i)) =
    if j=i then
      (((s.2:ℝ)/k)*countReactionDensity c ((s.2:ℝ)/k) consume (s.1 i))*
        (W (fun a => generalConcentration s i a+((produce a:ℝ)-(consume a:ℝ))/((s.2:ℝ)/k))-
          W (generalConcentration s i)) else 0 := by
  by_cases h : j=i
  · subst j
    have hc : generalConcentration (generalResidentNext s i consume produce) i =
        (fun a => (countReactionNext consume produce (s.1 i) a:ℝ)/((s.2:ℝ)/k)) := by
      funext a
      simp [generalConcentration,generalResidentNext]
    rw [hc,if_pos rfl]
    exact count_reaction_observable_binding consume produce (s.1 i) c ((s.2:ℝ)/k) W
  · have hij : i ≠ j := Ne.symm h
    have hc : generalConcentration (generalResidentNext s j consume produce) i=generalConcentration s i := by
      funext a
      simp [generalConcentration,generalResidentNext,hij]
    simp only [h,ite_false,hc,sub_self,mul_zero]

end CompositionalMemory
