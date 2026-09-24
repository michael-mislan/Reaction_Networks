import proofs.ProductiveMemory.ExtractionInitial
import proofs.ProductiveMemory.ExtractionSpatialProbability
import proofs.ProductiveMemory.ExtractionPartitionProbability

namespace ProductiveMemory
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal
noncomputable local instance ProductiveChemicalDecidableEq (D : Finset ProductiveState) : DecidableEq (ProductiveStopped D) := Classical.decEq _

noncomputable def productiveChemicalRawError (N : ℕ) (M t : ℝ) : ℝ :=
  let u := (N : ℝ)*localAlpha*readyLevel
  let drift := t*(16*M*(u/960)*Real.exp (u/2))
  Real.exp (-(8*u))*(M*Real.exp u+14*M*Real.exp (4*u)+drift)+
    Real.exp (-(2*u))*(M*Real.exp u+drift)+7*M*partitionError N

theorem productive_remove_exponential_barrier (a p B : ℝ) (h : Real.exp a*p ≤ B) :
    p ≤ Real.exp (-a)*B := by
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-a)).le
  have hc : Real.exp (-a)*(Real.exp a*p)=p := by
    rw [← mul_assoc,← Real.exp_add]
    simp
  rwa [hc] at hm

theorem productive_global_chemical_probability (N M W0 J : ℕ) (hN : 1 ≤ N) (hW : W0 ≤ 2*N*M)
    (hlarge : (200000000000000000000 : ℝ) ≤ N)
    (rho zL zH γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (hsL : extractDrift rho 0 (lift rho zL)=0)
    (hsH : extractDrift rho 0 (lift rho zH)=0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (productiveStoppedModel rho γ (by linarith [hr.1]) hγ (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).total x ≤ q)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH))
    (hready : ProductiveReadyPopulation N M rho zL zH s.val) :
    let P := (productiveStoppedModel rho γ (by linarith [hr.1]) hγ (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).uniformize q hq hbound
    P.poissonized (q*t) (FiniteKernel.eventIndicator (productiveOuterFailure N W0 J rho zL zH _)) (.inl s)+
      P.poissonized (q*t) (FiniteKernel.eventIndicator (productiveDivisionFailure N W0 J rho zL zH _)) (.inl s)+
      P.poissonized (q*t) (FiniteKernel.eventIndicator (productivePartitionFailureSet N W0 J rho zL zH _)) (.inl s) ≤
      productiveChemicalRawError N M t := by
  classical
  dsimp only
  have ho := productive_outer_failure_bound N M W0 J hN hlarge rho zL zH γ hr hzL hzH hsL hsH hγ hγmax q t hq hbound s
  have hd := productive_division_failure_bound N M W0 J hN hlarge rho zL zH γ hr hzL hzH hsL hsH hγ hγmax q t hq hbound s
  have hp := productive_global_partition_failure_bound γ hγ (4*W0) N M W0 J (by omega) hW rho zL zH hr hzL hzH q t hq hbound s
  have ho' := productive_remove_exponential_barrier _ _ _
    (ho.trans (add_le_add (productive_initial_outer_with_reserve N M rho zL zH s.val hready) le_rfl))
  have hd' := productive_remove_exponential_barrier _ _ _
    (hd.trans (add_le_add (productive_initial_spatial_bound N M rho zL zH s.val hready) le_rfl))
  simp only [productivePartitionReserve,hready.2.1,Nat.cast_zero,sub_zero] at hp
  have h := add_le_add (add_le_add ho' hd') hp
  convert h using 1
  unfold productiveChemicalRawError
  ring

end ProductiveMemory
