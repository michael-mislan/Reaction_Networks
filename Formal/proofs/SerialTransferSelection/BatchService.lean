import proofs.SerialTransferSelection.BatchJointProbability
import proofs.SerialTransferSelection.ServiceJoint

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal
noncomputable local instance BatchServiceDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) := Classical.decEq _

theorem phase_source_batch_with_service (N M W0 J : ℕ) (hJ : 0 < J) (hN : 1000 ≤ N) (hM : 0 < M) (hW : W0 ≤ 2*N*M)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH γ : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hγ : 0 < γ) (hγmax : γ ≤ 1/100000000000)
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (phaseStoppedModel γ hγ.le (4*W0) N W0 zL zH
      (phaseActiveDomain N M W0 zL zH)).total x ≤ q)
    (s : ActiveState (phaseActiveDomain N M W0 zL zH))
    (hready : PhaseReadyPopulation N M zL zH s.val)
    (hstart : membrane s.val.live=W0)
    (hH : 0 < ancestralMembrane true s.val.live)
    (hL : 0 < ancestralMembrane false s.val.live)
    (hkq : (9/40000)*(N : ℝ)*γ ≤ q) (htime : (t : ℝ)=8/γ) :
    let P := (serviceCounterModel (phaseStoppedModel γ hγ.le (4*W0) N W0 zL zH
      (phaseActiveDomain N M W0 zL zH)) J).uniformize q hq (fun x => hbound x.1)
    1-(phaseChemicalRawError N M t+Real.exp (-(N : ℝ)/2500)+Real.exp (-(19*(N : ℝ)/500000))+(t : ℝ)*q/J) ≤
      P.poissonized (q*t) (FiniteKernel.eventIndicator
        {x | x.1 ∈ phaseBatchGoodSet N W0 (ancestralMembrane true s.val.live)
          (ancestralMembrane false s.val.live) zL zH (phaseActiveDomain N M W0 zL zH) ∧ x.2.val < J}) (.inl s, 0) := by
  classical
  dsimp only
  have hs := phase_source_batch_joint_return N M W0 hN hM hW hlarge zL zH γ
    hzL hzH hsL hsH hγ hγmax q t hq hbound s hready hstart hH hL hkq htime
  have hj := service_joint_lower
    (phaseStoppedModel γ hγ.le (4*W0) N W0 zL zH (phaseActiveDomain N M W0 zL zH)) J
    hJ q t hq hbound (phaseBatchGoodSet N W0 (ancestralMembrane true s.val.live)
      (ancestralMembrane false s.val.live) zL zH (phaseActiveDomain N M W0 zL zH)) (.inl s)
  dsimp only at hs
  linarith only [hs,hj]

end SerialTransferSelection
