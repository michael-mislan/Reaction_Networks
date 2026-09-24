import proofs.CompositionalMemory.CountBinding

namespace CompositionalMemory
open FiniteCopy

theorem exchange_concentration_local {k : ℕ} (s : ModularCountState k)
    (i j l : Fin k) (hne : j ≠ l) (hn : 1 ≤ s.1 j 2) :
    modularConcentration (modularNext s (.inr (.inl (j,l)))) i =
      if j=i then (fun a => modularConcentration s i a+(if a=2 then (-1 : ℝ) else 0)/((s.2 : ℝ)/k))
      else if l=i then (fun a => modularConcentration s i a+(if a=2 then (1 : ℝ) else 0)/((s.2 : ℝ)/k))
      else modularConcentration s i := by
  by_cases hj : j=i
  · subst j
    simpa [modularNext,modularConcentration,hne,Ne.symm hne] using
      consuming_effective_concentration ((s.2 : ℝ)/k) (s.1 i) hn
  · by_cases hl : l=i
    · subst l
      simpa [modularNext,modularConcentration,hj] using
        receiving_effective_concentration ((s.2 : ℝ)/k) (s.1 i)
    · have hij := Ne.symm hj
      have hil := Ne.symm hl
      simp_all [modularNext,modularConcentration]

theorem exchange_local_term {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hdiag : ∀ j, w j j=0) (s : ModularCountState k) (i j l : Fin k) (W : Point → ℝ) :
    modularRate γ w s (.inr (.inl (j,l)))*
      (W (modularConcentration (modularNext s (.inr (.inl (j,l)))) i)-W (modularConcentration s i)) =
      (if j=i then w j l*(s.1 j 2 : ℝ)*
        (W (fun a => modularConcentration s i a+(if a=2 then (-1 : ℝ) else 0)/((s.2 : ℝ)/k))-
          W (modularConcentration s i)) else 0) +
      (if l=i then w j l*(s.1 j 2 : ℝ)*
        (W (fun a => modularConcentration s i a+(if a=2 then (1 : ℝ) else 0)/((s.2 : ℝ)/k))-
          W (modularConcentration s i)) else 0) := by
  by_cases hne : j=l
  · subst l
    simp [modularRate,modularNext,hdiag]
  · by_cases hn : 1 ≤ s.1 j 2
    · rw [exchange_concentration_local s i j l hne hn]
      by_cases hj : j=i
      · subst j
        simp [modularRate,Ne.symm hne]
      · by_cases hl : l=i
        · subst l; simp [modularRate,hj]
        · simp [modularRate,hj,hl]
    · have hn0 : s.1 j 2=0 := by omega
      simp [modularRate,hn0]

end CompositionalMemory
