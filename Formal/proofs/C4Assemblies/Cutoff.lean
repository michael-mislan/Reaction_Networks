import proofs.C4Assemblies.BudgetSafety

namespace C4Assemblies
noncomputable section
open ProductiveRecovery
variable {ι : Type*} [Fintype ι]

/-- The actual source trajectory also solves the cutoff apparatus through its funded interval. -/
theorem source_prefix_cutoff_agreement (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyAdmitted c) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c) (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t)
    (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    HasDerivAt X
      (maintainedWithCutoff (assemblyField P.k P.r P.d (X t))
        (sharedFoodUPrefix p t) (sharedFoodWPrefix p t) (sharedServicePrefix P X t)
        ((Fintype.card ι : ℝ)*(T+151/200))
        ((Fintype.card ι : ℝ)*(T+151/200))
        ((Fintype.card ι : ℝ)*(9/200)*T)) t := by
  obtain ⟨hu,hw,hg⟩ := source_prefix_allowances P p c hc X h0 hn hX t T ht htT
  rw [allocated_cutoff_agrees _ _ _ _ _ _ _ hu hw hg]
  exact hX t ht

end
end C4Assemblies
