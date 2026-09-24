import proofs.CompositionalMemory.GenericMembraneCountBinding

namespace CompositionalMemory

theorem general_exchange_concentration {k d : ℕ} (z : Fin d) (s : GeneralCountState k d)
    (i j l : Fin k) (hne : j ≠ l) (hn : 1 ≤ s.1 j z) :
    generalConcentration (generalExchangeNext z s j l) i =
      if j=i then generalConcentration s i+(1/((s.2:ℝ)/k)) • (-(fun a => if a=z then (1:ℝ) else 0))
      else if l=i then generalConcentration s i+(1/((s.2:ℝ)/k)) • (fun a => if a=z then (1:ℝ) else 0)
      else generalConcentration s i := by
  have hz : s.1 j z ≠ 0 := by omega
  by_cases hj : j=i
  · subst j
    funext a
    simp [generalExchangeNext,hne,hz,generalConcentration,
      unit_consumption_count_cast z (s.1 i) hn a]
    split_ifs <;> ring_nf
    all_goals (simp only [inv_inv]; ring)
  · by_cases hl : l=i
    · subst l
      funext a
      simp [generalExchangeNext,hne,hz,generalConcentration,countReactionNext,speciesUnit]
      split_ifs <;> ring_nf
      all_goals (simp only [inv_inv]; ring)
    · funext a
      simp [generalExchangeNext,hne,hz,generalConcentration,hj,hl,Ne.symm hj,Ne.symm hl]

theorem general_exchange_observable_local {k d : ℕ} (z : Fin d) (s : GeneralCountState k d)
    (w : Fin k → Fin k → ℝ) (hdiag : ∀ j, w j j=0) (i j l : Fin k)
    (W : (Fin d → ℝ) → ℝ) :
    (w j l*(s.1 j z:ℝ))*(W (generalConcentration (generalExchangeNext z s j l) i)-W (generalConcentration s i)) =
      (if j=i then (w j l*(s.1 i z:ℝ))*
        (W (generalConcentration s i+(1/((s.2:ℝ)/k)) • (-(fun a => if a=z then (1:ℝ) else 0)))-W (generalConcentration s i)) else 0)+
      (if l=i then (w j l*(s.1 j z:ℝ))*
        (W (generalConcentration s i+(1/((s.2:ℝ)/k)) • (fun a => if a=z then (1:ℝ) else 0))-W (generalConcentration s i)) else 0) := by
  by_cases hne : j=l
  · subst l
    simp [hdiag]
  · by_cases hn : 1 ≤ s.1 j z
    · rw [general_exchange_concentration z s i j l hne hn]
      by_cases hj : j=i
      · subst j
        simp [Ne.symm hne]
      · by_cases hl : l=i
        · subst l; simp [hj]
        · simp [hj,hl]
    · have hz : s.1 j z=0 := by omega
      by_cases hj : j=i
      · subst j; simp [hz]
      · simp [hj,hz]

end CompositionalMemory
