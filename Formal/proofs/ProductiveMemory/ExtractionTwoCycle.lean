import proofs.ProductiveMemory.ExtractionCycleKernel
import proofs.SerialTransferSelection.PopulationPhase
import proofs.SerialTransferSelection.ParameterMargins

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false

abbrev ProductiveTwoResult (N M J : ℕ) (rho zL zH : ℝ) := ProductiveCycleResult N M J rho zL zH × Fin J

def productiveTwoRelation (N M J : ℕ) (rho zL zH : ℝ) (s : ProductiveState) (eps : ℝ)
    (y : ProductiveTwoResult N M J rho zL zH) : Prop :=
  (∀ b, 0 < ancestralCount b y.1.1.val.population.live) ∧
  2*SerialTransferSelection.cycleSizeGain eps <
    SerialTransferSelection.sizeLogOdds y.1.1.val.population-SerialTransferSelection.sizeLogOdds s.population ∧
  5*membrane s.population.live < y.2.val ∧ 5*(N*M) < y.1.2.val

variable (N M : ℕ) (hN : 1 ≤ N) (hM : 0 < M) (hlarge : recoveryCount ≤ N) (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (gamma : ℝ) (hg : 0 < gamma) (t : NNReal)

abbrev productiveJ := productiveCollectionQuota N M rho t

def productiveSecondKernel (x : Option (ProductiveCycleResult N M (productiveJ N M rho t) rho zL zH)) :
    FiniteLaw (Option (ProductiveTwoResult N M (productiveJ N M rho t) rho zL zH)) :=
  match x with
  | none => FiniteLaw.pure none
  | some y => productiveRecordOutput (productiveJ N M rho t) y.2
      (productiveCycleKernel N M hN hM hlarge rho zL zH hr hzL hzH gamma hg t y.1)

def productiveTwoCycleLaw (s : ProductiveReady N M rho zL zH) :
    FiniteLaw (Option (ProductiveTwoResult N M (productiveJ N M rho t) rho zL zH)) :=
  (productiveCycleKernel N M hN hM hlarge rho zL zH hr hzL hzH gamma hg t s).bind
    (productiveSecondKernel N M hN hM hlarge rho zL zH hr hzL hzH gamma hg t)

theorem productive_two_cycle_probability
    (hsL : extractDrift rho 0 (lift rho zL)=0) (hsH : extractDrift rho 0 (lift rho zH)=0)
    (hgmax : gamma ≤ 1/100000000000) (htime : (t:ℝ)=8/gamma)
    (p₀ p₁ eps : ℝ) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (heps : 0 < eps) (heps1 : eps < 1)
    (hnext : p₁ ≤ (1-eps)*p₀/16) (s : ProductiveReady N M rho zL zH)
    (hfloor : ∀ b, p₀*(M:ℝ) ≤ ancestralCount b s.val.population.live) :
    1-(productiveCycleError N M t p₀ eps+productiveCycleError N M t p₁ eps) ≤
      (productiveTwoCycleLaw N M hN hM hlarge rho zL zH hr hzL hzH gamma hg t s).expect
        (FiniteKernel.eventIndicator (SerialTransferSelection.successfulOutput
          (productiveTwoRelation N M (productiveJ N M rho t) rho zL zH s.val eps))) := by
  classical
  unfold productiveTwoCycleLaw
  apply SerialTransferSelection.finiteLaw_joint_bind_lower _ _
    (SerialTransferSelection.successfulOutput (productiveCycleRelation N M (productiveJ N M rho t) rho zL zH s.val p₀ eps)) _ _ _
    (by unfold productiveCycleError productiveChemicalRawError partitionError localAlpha readyLevel outerLevel; positivity)
  · exact productive_cycle_kernel_probability N M hN hM hlarge rho zL zH hr hzL hzH gamma hg t
      hsL hsH hgmax htime p₀ eps hp₀ heps heps1 s hfloor
  · intro o ho
    cases o with
    | none => exact False.elim ho
    | some y =>
      change productiveCycleRelation N M (productiveJ N M rho t) rho zL zH s.val p₀ eps y at ho
      have hyfloor (b : Bool) : p₁*(M:ℝ) ≤ ancestralCount b y.1.val.population.live := by
        exact (le_div_iff₀ (by positivity : (0:ℝ)<M)).mp (hnext.trans (ho.1 b).2)
      change (1-productiveCycleError N M t p₁ eps) ≤
        (productiveRecordOutput _ y.2 _).expect _
      rw [productive_record_probability]
      have hc := productive_cycle_kernel_probability N M hN hM hlarge rho zL zH hr hzL hzH gamma hg t
        hsL hsH hgmax htime p₁ eps hp₁ heps heps1 y.1 hyfloor
      apply hc.trans
      apply SerialTransferSelection.finiteLaw_successful_mono
      intro z hz
      refine ⟨fun b => (hz.1 b).1,?_,ho.2.2,?_⟩
      · linarith only [ho.2.1,hz.2.1]
      · exact (Nat.mul_le_mul_left 5 (productive_ready_membrane_lower N M rho zL zH y.1)).trans_lt hz.2.2

end
end ProductiveMemory
