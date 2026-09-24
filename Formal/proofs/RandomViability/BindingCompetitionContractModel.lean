import proofs.RandomViability.BindingCompetitionHorizonComposition

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

structure CompetitionRateBox where
  K : ℝ
  r : ℝ
  delta : ℝ
  K_lower : 8 ≤ K
  K_upper : K ≤ 12
  r_lower : 18 ≤ r
  r_upper : r ≤ 22
  delta_lower : 1/100 ≤ delta
  delta_upper : delta ≤ 1/20

theorem CompetitionRateBox.inv_nonneg (p : CompetitionRateBox) : 0 ≤ 1/p.K := by
  have := p.K_lower
  positivity

theorem CompetitionRateBox.inv_upper (p : CompetitionRateBox) : 1/p.K ≤ 1/8 := by
  exact one_div_le_one_div_of_le (by norm_num) p.K_lower

theorem CompetitionRateBox.r_nonneg (p : CompetitionRateBox) : 0 ≤ p.r := by have := p.r_lower; linarith
theorem CompetitionRateBox.delta_nonneg (p : CompetitionRateBox) : 0 ≤ p.delta := by have := p.delta_lower; linarith
theorem CompetitionRateBox.delta_local (p : CompetitionRateBox) : p.delta ≤ 3/5 := by have := p.delta_upper; linarith

def competitionContractModel (V : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ)) :=
  competitionModel V (1/500000000) (1/p.K) p.r p.delta hV (by norm_num) p.inv_nonneg p.r_nonneg p.delta_nonneg

def competitionContractWindowModel (V : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ)) :=
  competitionWindowModel V (competitionWindowCap V) (1/500000000) (1/p.K) p.r p.delta
    hV (by norm_num) p.inv_nonneg p.r_nonneg p.delta_nonneg

def competitionClock (V : ℕ) : ℕ := 3000*V

theorem competitionClock_pos (V : ℕ) (hV : 0 < (V:ℝ)) : 0 < competitionClock V := by
  have hv : 0 < V := by exact_mod_cast hV
  unfold competitionClock
  positivity

theorem competition_contract_total (V : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ)) (X : CompetitionCounts V) :
    (competitionContractModel V p hV).total X ≤ (competitionClock V:ℝ) := by
  simpa only [competitionContractModel,competitionClock,Nat.cast_mul,Nat.cast_ofNat] using
    competition_model_total V (1/500000000) (1/p.K) p.r p.delta hV (by norm_num) (by norm_num)
      p.inv_nonneg p.inv_upper p.r_nonneg p.r_upper p.delta_nonneg p.delta_local X

theorem competition_contract_window_total (V : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ))
    (X : CompetitionWindowState V (competitionWindowCap V)) :
    (competitionContractWindowModel V p hV).total X ≤ (competitionClock V:ℝ) := by
  simpa only [competitionContractWindowModel,competitionClock,Nat.cast_mul,Nat.cast_ofNat] using
    competition_window_total V (competitionWindowCap V) (1/500000000) (1/p.K) p.r p.delta hV
      (by norm_num) (by norm_num) p.inv_nonneg p.inv_upper p.r_nonneg p.r_upper p.delta_nonneg p.delta_local X

def competitionContractKernel (V : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ)) : FiniteKernel (CompetitionCounts V) :=
  (competitionContractModel V p hV).uniformize (competitionClock V)
    (by exact_mod_cast competitionClock_pos V hV) (competition_contract_total V p hV)

def competitionContractWindowKernel (V : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ)) :
    FiniteKernel (CompetitionWindowState V (competitionWindowCap V)) :=
  (competitionContractWindowModel V p hV).uniformize (competitionClock V)
    (by exact_mod_cast competitionClock_pos V hV) (competition_contract_window_total V p hV)

def competitionDuration (V : ℕ) : ℝ := Real.exp ((V:ℝ)/1000000)
def competitionWindowNumber (V : ℕ) : ℕ := ⌊competitionDuration V⌋₊
def competitionFraction (V : ℕ) : ℝ≥0 :=
  ⟨competitionDuration V-(competitionWindowNumber V:ℝ),sub_nonneg.mpr (Nat.floor_le (Real.exp_pos _).le)⟩

theorem competition_horizon_partition (V : ℕ) :
    (competitionWindowNumber V:ℝ)+(competitionFraction V:ℝ)=competitionDuration V := by
  change (competitionWindowNumber V:ℝ)+(competitionDuration V-(competitionWindowNumber V:ℝ))=competitionDuration V
  ring

theorem competition_fraction_lt_one (V : ℕ) : (competitionFraction V:ℝ)<1 := by
  have h := Nat.lt_floor_add_one (competitionDuration V)
  change competitionDuration V-(competitionWindowNumber V:ℝ)<1
  unfold competitionWindowNumber
  linarith

/-- Actual source, fixed epsilon, reciprocal K, certified clock and real horizon.
Supply events are not yet included in this operating-failure observable. -/
def competitionContractOperatingFailure (V : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ)) : ℝ :=
  competitionHorizonFailure V (competitionContractKernel V p hV) (competitionContractWindowKernel V p hV)
    (competitionClock V) (competitionFraction V) (competitionWindowNumber V) (competitionFoodInitial V hV)

theorem competition_contract_operating_bound (V : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ)) :
    competitionContractOperatingFailure V p hV ≤
      Real.exp (-(8047/312500000000)*(V:ℝ))+Real.exp (-3000*(V:ℝ)/500000)+
      4*Real.exp (-(V:ℝ)/1000)+Real.exp (-(V:ℝ)/62500)+
      (500+competitionDuration V)*(4*resourceSource V+competitionReturnSource V)+
      (competitionWindowNumber V:ℝ)*Real.exp (1/8-(13/1080000)*(V:ℝ)) := by
  have he (N : BoxCounts V) :
      (competitionEntryModel V ((V:ℝ)/2500) (1/500000000) (1/p.K) p.r p.delta hV
        (by norm_num) p.inv_nonneg p.r_nonneg p.delta_nonneg).total N ≤ (competitionClock V:ℝ) := by
    simpa only [competitionClock,Nat.cast_mul,Nat.cast_ofNat] using
      competition_entry_total_bound V ((V:ℝ)/2500) (1/500000000) (1/p.K) p.r p.delta hV
        (by norm_num) (by norm_num) p.inv_nonneg p.inv_upper p.r_nonneg p.r_upper p.delta_nonneg p.delta_local N
  have hc : (V:ℝ)/27000 ≤ (competitionClock V:ℝ) := by
    simp only [competitionClock,Nat.cast_mul,Nat.cast_ofNat]
    linarith
  have hh := competition_startup_horizon V (competitionClock V) (1/500000000) (1/p.K) p.r p.delta hV
    (by norm_num) (by norm_num) p.inv_nonneg p.inv_upper p.r_lower p.r_upper p.delta_nonneg p.delta_local
    (competitionClock_pos V hV) hc (competition_contract_total V p hV) he (competition_contract_window_total V p hV)
    (competitionFraction V) (competitionWindowNumber V)
  rw [competition_entry_exponent] at hh
  have ht : 500+(competitionWindowNumber V:ℝ)+(competitionFraction V:ℝ)=500+competitionDuration V := by
    linarith [competition_horizon_partition V]
  rw [ht] at hh
  simpa only [competitionContractOperatingFailure,competitionContractKernel,competitionContractWindowKernel,
    competitionContractModel,competitionContractWindowModel,competitionClock,Nat.cast_mul,Nat.cast_ofNat,neg_mul] using hh

end
end RandomViability.Binding
