import proofs.SerialTransferSelection.ChemicalEnvelope
import proofs.SerialTransferSelection.GeometricEligibility

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Filter Topology

/-- Every prescribed finite horizon admits finite source parameters at 99%.
The source existence theorem consumes exactly this algebraic contract. -/
theorem exists_manyCycle_parameters (K : ℕ) :
    ∃ (N B : ℕ) (δ : ℝ), 140000000000000000000 ≤ N ∧ 0 < B ∧ 0 < δ ∧
      ∀ (JB JR : ℕ) (qb qr : ℝ), candidateTime*qb/JB < δ →
        ((2*B : ℕ) : ℝ)*(5376*qr/JR) < δ →
        historyBudget (fun j => sourceCycleError N (2*B) JB JR qb qr
          candidateTime (baselineFloor j) (1/50)) K 0 < 1/100 := by
  obtain ⟨B,hB,htrans⟩ := exists_baseline_population K (1/1000) (by norm_num)
  let δ : ℝ := 1/(1000*((K : ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlim := chemicalCycleError_tendsto (2*B) candidateTime (by norm_num [candidateTime])
  have he : ∀ᶠ N : ℕ in atTop, chemicalCycleError N (2*B) candidateTime < δ :=
    (tendsto_order.mp hlim).2 δ hδ
  obtain ⟨N,hlarge,hchem⟩ := ((eventually_ge_atTop 140000000000000000000).and he).exists
  refine ⟨N,B,δ,hlarge,hB,hδ,?_⟩
  intro JB JR qb qr hb hr
  rw [baseline_geometric_budget N (2*B) JB JR K (by omega)]
  have hk : (K : ℝ)*δ < 1/1000 := by
    dsimp [δ]
    have hd : (0 : ℝ) < 1000*((K : ℝ)+1) := by positivity
    rw [mul_one_div]
    apply (div_lt_iff₀ hd).mpr
    linarith
  have hsum : chemicalCycleError N (2*B) candidateTime+
      candidateTime*qb/JB+((2*B : ℕ) : ℝ)*(5376*qr/JR) ≤ 3*δ := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
  nlinarith only [hmul,hk,htrans]

end SerialTransferSelection
