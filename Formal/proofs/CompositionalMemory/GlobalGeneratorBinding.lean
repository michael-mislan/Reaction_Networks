import proofs.CompositionalMemory.ExchangeBinding

namespace CompositionalMemory
open FiniteCopy

/-- Exact docking of the full count process to one local observer. -/
theorem global_local_generator {k : ℕ} (hk : 1 ≤ k) (γ : ℝ)
    (w : Fin k → Fin k → ℝ) (hdiag : ∀ j, w j j=0)
    (hsym : ∀ j l, w j l=w l j) (s : ModularCountState k)
    (hm : 0 < s.2) (i : Fin k) (W : Point → ℝ) :
    modularGenerator γ w (fun t => W (modularConcentration t i)) s =
      coupledLocalGenerator γ (s.2 : ℝ) (w i) i s.1 W := by
  classical
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hmpos : (0 : ℝ) < s.2 := by exact_mod_cast hm
  have hrate (j : Fin k) :
      ((s.2 : ℝ)/k)*modularConcentration s j 2 = (s.1 j 2 : ℝ) := by
    dsimp [modularConcentration,effectiveConcentration]
    field_simp
  simp only [modularGenerator,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp_rw [resident_local_term,exchange_local_term γ w hdiag,membrane_local_term hk γ w s hm]
  simp only [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_const_zero]
  simp only [coupledLocalGenerator,effectiveGenerator,Fintype.sum_sum_type,
    incidentRate,localIncidentJump,Sum.elim_inl,Sum.elim_inr]
  have hx (j : Fin k) : effectiveConcentration ((s.2 : ℝ)/k) (s.1 j) =
      modularConcentration s j := rfl
  simp only [hx]
  simp_rw [show ∀ j, ((s.2 : ℝ)/k)*w i j*modularConcentration s i 2 =
      w i j*(s.1 i 2 : ℝ) by intro j; calc
        _ = w i j*(((s.2 : ℝ)/k)*modularConcentration s i 2) := by ring
        _ = _ := by rw [hrate],
    show ∀ j, ((s.2 : ℝ)/k)*w i j*modularConcentration s j 2 =
      w j i*(s.1 j 2 : ℝ) by intro j; calc
        _ = w i j*(((s.2 : ℝ)/k)*modularConcentration s j 2) := by ring
        _ = _ := by rw [hrate,hsym i j]]
  simp only [Finset.mul_sum,mul_assoc]
  ring

end CompositionalMemory
