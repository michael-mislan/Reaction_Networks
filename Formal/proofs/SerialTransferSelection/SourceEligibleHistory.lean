import proofs.SerialTransferSelection.ManyCycleShare
import proofs.SerialTransferSelection.EligibleHistory
import proofs.SerialTransferSelection.ManyCycleParameters

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

variable (N M JB JR : ℕ) (hN : 1 ≤ N) (hM : 0 < M) (zL zH : ℝ)
  (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
  (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
  (qr : NNReal) (hqr : 0 < (qr : ℝ))
  (hclockr : ∀ tag x, (recoveryCellModel N zL zH tag).total x ≤ qr)
  (γ : ℝ) (hγ : 0 ≤ γ) (qb t : NNReal) (hqb : 0 < (qb : ℝ))
  (hclockb : ∀ (s : ReadyPopulation N M zL zH) x,
    (cycleBatchModel N M zL zH γ hγ s).total x ≤ qb)

theorem sourceManyCycleLaw_eligible_probability
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hlarge : (140000000000000000000 : ℝ) ≤ N) (h1000 : 1000 ≤ N)
    (hJB : 0 < JB) (hJR : 0 < JR) (hγpos : 0 < γ) (hγmax : γ ≤ 1/100000000000)
    (hkr : (N : ℝ)*localAlpha*innerEnergy/672 ≤ qr)
    (hkb : (9/40000)*(N : ℝ)*γ ≤ qb) (htime : (t : ℝ)=8/γ)
    (q ε : ℝ) (hq : 0 < q) (hε : 0 < ε) (hε1 : ε < 1)
    (K : ℕ) (s : ReadyPopulation N M zL zH) :
    1-(K : ℝ)*shareCycleError N M JB JR qb qr t q ε ≤
      (sourceManyCycleLaw N M JB JR hN hM zL zH hzL hzH qr hqr hclockr
        γ hγ qb t hqb hclockb K s).expect
        (FiniteKernel.eventIndicator {h | eligibleHistoryGood
          (shareHistoryEligible N M zL zH (fun _ => q))
          (shareHistoryStep N M zL zH (fun _ => q) ε) K 0 (some s) h}) := by
  rw [← historyBudget_const (shareCycleError N M JB JR qb qr t q ε) K 0]
  apply eligibleHistory_probability
  · intro j
    unfold shareCycleError phaseChemicalRawError recoveryError partitionError localAlpha innerEnergy outerEnergy
    positivity
  · intro j x hx
    cases x with
    | none => exact False.elim hx
    | some y =>
      have he : {v | shareHistoryStep N M zL zH (fun _ => q) ε j (some y) v} =
          successfulOutput (shareCycleReadyRelation N M zL zH y.val q ε) := by
        ext v
        cases v <;> rfl
      rw [he]
      exact sourceCycleLaw_share_probability N M JB JR hN hM zL zH hzL hzH y qr hqr hclockr
        hsL hsH hlarge hJR hkr q ε hq hε hε1 hx h1000 hJB
        γ hγpos hγmax qb t hqb (hclockb y) hkb htime

end SerialTransferSelection
