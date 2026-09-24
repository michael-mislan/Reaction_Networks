import proofs.SerialTransferSelection.HorizonScaling
import proofs.SerialTransferSelection.ManyCycleShareInstance

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

/-- The complete source-law conclusion, with all physical inputs and quotas existentially bound. -/
def SourceMissionAvailable (N B K : ℕ) (δ confidence : ℝ) : Prop :=
    ∃ (_hN : 1 ≤ N) (_hB : 0 < B),
    ∃ (zL zH : ℝ)
      (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
      (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)),
      Stationary sourceRates (lift sourceRates zL) ∧ Stationary sourceRates (lift sourceRates zH) ∧
      ∃ (JB JR : ℕ) (qb qr : NNReal) (hqb : 0 < (qb : ℝ)) (hqr : 0 < (qr : ℝ))
        (hclockr : ∀ tag x, (recoveryCellModel N zL zH tag).total x ≤ qr)
        (hclockb : ∀ (s : ReadyPopulation N (2*B) zL zH) x,
          (cycleBatchModel N (2*B) zL zH candidateGamma (by norm_num [candidateGamma]) s).total x ≤ qb)
        (s : ReadyPopulation N (2*B) zL zH),
        0 < JB ∧ 0 < JR ∧ candidateTime*(qb : ℝ)/JB < δ ∧
        ((2*B : ℕ) : ℝ)*(5376*(qr : ℝ)/JR) < δ ∧
        (∀ b, chemicalCount b s.val.live=B) ∧
        (∀ c ∈ s.val.live, c.compartment.2=N) ∧
        confidence ≤
          (sourceManyCycleLaw N (2*B) JB JR (by omega) (by omega) zL zH hzL hzH
            qr hqr hclockr candidateGamma (by norm_num [candidateGamma])
            qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb K s).expect
            (FiniteKernel.eventIndicator (manyMeasuredEvent N (2*B) zL zH (1/50) K s.val))

theorem source_horizon_design (N B K : ℕ)
    (hN : 140000000000000000000 ≤ N) (hB : 0 < B) (hK : 0 < K)
    (δ : ℝ) (hδ : 0 < δ)
    (htransfer : (K : ℝ) ≤ Real.log (1+(δ/3)*(204/49-1)*((2*B : ℕ) : ℝ)/80000)/Real.log (204/49))
    (hsize : 4*Real.log ((142+4*candidateTime/21)*((2*B : ℕ) : ℝ)*(K : ℝ)/(δ/3)) ≤
      (N : ℝ)*localAlpha*innerEnergy) :
    SourceMissionAvailable N B K (δ/(6*(K+1))) (1-δ) := by
  refine ⟨by omega,hB,?_⟩
  apply manyCycle_share_instance N B K hN hB (δ/(6*(K+1))) (1-δ) (by positivity)
  intro JB JR qb qr hb hr
  rw [share_geometric_budget _ _ _ _ _ (by omega)]
  have ht := (transfer_inverse_horizon (2*B) K (by omega) (δ/3) (by positivity)).mpr htransfer
  have hc := chemical_sizing N (2*B) K (by omega) hK candidateTime (δ/3)
    (by norm_num [candidateTime]) (by positivity) hsize
  have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hb' := mul_le_mul_of_nonneg_left hb.le hk
  have hr' := mul_le_mul_of_nonneg_left hr.le hk
  have hs : (K : ℝ)*(δ/(6*(K+1))) < δ/6 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (show (0 : ℝ) < 6*(K+1) by positivity)).mpr
    nlinarith
  nlinarith

/-- At fixed confidence and even population, the logarithmic horizon condition has actual source instances. -/
theorem logarithmic_source_horizon (B K : ℕ) (hB : 0 < B) (hK : 0 < K)
    (δ : ℝ) (hδ : 0 < δ)
    (htransfer : (K : ℝ) ≤ Real.log (1+(δ/3)*(204/49-1)*((2*B : ℕ) : ℝ)/80000)/Real.log (204/49)) :
    ∃ N : ℕ, SourceMissionAvailable N B K (δ/(6*(K+1))) (1-δ) := by
  let A := 4*Real.log ((142+4*candidateTime/21)*((2*B : ℕ) : ℝ)*(K : ℝ)/(δ/3))
  obtain ⟨N,hN⟩ := exists_nat_gt (max (140000000000000000000 : ℝ) (A/(localAlpha*innerEnergy)))
  have hn : (140000000000000000000 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hs : A/(localAlpha*innerEnergy) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have ha : 0 < localAlpha*innerEnergy := by norm_num [localAlpha,innerEnergy,outerEnergy]
  have hh := (div_lt_iff₀ ha).mp hs
  refine ⟨N,source_horizon_design N B K ?_ hB hK δ hδ htransfer ?_⟩
  · exact_mod_cast hn.le
  · dsimp [A] at hh
    nlinarith

end SerialTransferSelection
