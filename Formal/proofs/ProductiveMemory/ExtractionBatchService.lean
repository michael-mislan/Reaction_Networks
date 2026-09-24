import proofs.ProductiveMemory.ExtractionJointProbability
import proofs.SerialTransferSelection.ServiceJoint

namespace ProductiveMemory
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal
noncomputable local instance ProductiveBatchServiceDecEq (D : Finset ProductiveState) : DecidableEq (ProductiveStopped D) := Classical.decEq _

theorem productive_batch_with_service (N M W0 J JS : ℕ) (hJ : 0 < J) (hJS : 0 < JS) (hN : 1000 ≤ N) (hM : 0 < M) (hW : W0 ≤ 2*N*M)
    (hlarge : (200000000000000000000 : ℝ) ≤ N)
    (rho zL zH γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (hsL : extractDrift rho 0 (lift rho zL)=0)
    (hsH : extractDrift rho 0 (lift rho zH)=0)
    (hγ : 0 < γ) (hγmax : γ ≤ 1/100000000000)
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (productiveStoppedModel rho γ (by linarith [hr.1]) hγ.le (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).total x ≤ q)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH))
    (hready : ProductiveReadyPopulation N M rho zL zH s.val)
    (hstart : membrane s.val.population.live=W0)
    (hH : 0 < ancestralMembrane true s.val.population.live)
    (hL : 0 < ancestralMembrane false s.val.population.live)
    (hkq : (9/40000)*(N : ℝ)*γ ≤ q) (htime : (t : ℝ)=8/γ) :
    let P := (SerialTransferSelection.serviceCounterModel (productiveStoppedModel rho γ (by linarith [hr.1]) hγ.le (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)) JS).uniformize q hq (fun x => hbound x.1)
    1-(productiveChemicalRawError N M t+Real.exp (-(N : ℝ)/2500)+Real.exp (-(19*(N : ℝ)/500000))+(t:ℝ)*(560*(N:ℝ)*(M:ℝ)*rho)/J+Real.exp (-(W0:ℝ))+(t:ℝ)*q/JS) ≤
      P.poissonized (q*t) (FiniteKernel.eventIndicator
        {x | x.1 ∈ productiveBatchGoodSet N W0 J (ancestralMembrane true s.val.population.live)
          (ancestralMembrane false s.val.population.live) rho zL zH (productiveActiveDomain N M W0 J rho zL zH) ∧ x.2.val < JS}) (.inl s,0) := by
  classical
  dsimp only
  have hbatch := productive_source_batch_joint_return N M W0 J hJ hN hM hW hlarge rho zL zH γ
    hr hzL hzH hsL hsH hγ hγmax q t hq hbound s hready hstart hH hL hkq htime
  have hservice := SerialTransferSelection.service_joint_lower
    (productiveStoppedModel rho γ (by linarith [hr.1]) hγ.le (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)) JS hJS q t hq hbound
      (productiveBatchGoodSet N W0 J (ancestralMembrane true s.val.population.live)
        (ancestralMembrane false s.val.population.live) rho zL zH (productiveActiveDomain N M W0 J rho zL zH)) (.inl s)
  dsimp only at hbatch
  linarith only [hbatch,hservice]

end ProductiveMemory
