import proofs.ProductiveMemory.ExtractionJointEvent

namespace ProductiveMemory
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal
noncomputable local instance ProductiveJointProbabilityDecEq (D : Finset ProductiveState) : DecidableEq (ProductiveStopped D) := Classical.decEq _

theorem productive_source_batch_joint_return (N M W0 J : ℕ) (hJ : 0 < J) (hN : 1000 ≤ N) (hM : 0 < M) (hW : W0 ≤ 2*N*M)
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
    let P := (productiveStoppedModel rho γ (by linarith [hr.1]) hγ.le (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).uniformize q hq hbound
    1-(productiveChemicalRawError N M t+Real.exp (-(N : ℝ)/2500)+Real.exp (-(19*(N : ℝ)/500000))+(t:ℝ)*(560*(N:ℝ)*(M:ℝ)*rho)/J+Real.exp (-(W0:ℝ))) ≤
      P.poissonized (q*t) (FiniteKernel.eventIndicator
        (productiveBatchGoodSet N W0 J (ancestralMembrane true s.val.population.live)
          (ancestralMembrane false s.val.population.live) rho zL zH (productiveActiveDomain N M W0 J rho zL zH))) (.inl s) := by
  classical
  dsimp only
  let D := productiveActiveDomain N M W0 J rho zL zH
  let P := (productiveStoppedModel rho γ (by linarith [hr.1]) hγ.le (4*W0) N W0 J zL zH D).uniformize q hq hbound
  let H0 := ancestralMembrane true s.val.population.live
  let L0 := ancestralMembrane false s.val.population.live
  have hw0 : H0+L0=W0 := (ancestral_membrane_total s.val.population.live).trans hstart
  have hc := productive_global_chemical_probability N M W0 J (by omega) hW hlarge rho zL zH γ
    hr hzL hzH hsL hsH hγ.le hγmax q t hq hbound s hready
  have hd := productive_global_deadline_probability γ hγ N M W0 J hN hM rho zL zH hr hzL hzH
    q t hq hbound hkq htime s hstart
  have ho := productive_global_odds_probability γ hγ.le (4*W0) N M W0 J hN rho zL zH hr hzL hzH
    q t hq hbound s hH hL
  have hu := productive_unflagged_probability γ hγ.le N M W0 J (by omega) hW rho zL zH hr hzL hzH
    q t hq hbound s
  have hpH := productive_ancestry_below_probability rho γ hγ.le (by linarith [hr.1]) (4*W0) N W0 J H0 zL zH D true
    q t hq hbound (.inl s) (le_refl _)
  have hpL := productive_ancestry_below_probability rho γ hγ.le (by linarith [hr.1]) (4*W0) N W0 J L0 zL zH D false
    q t hq hbound (.inl s) (le_refl _)
  have hquota := productive_quota_probability rho γ (by linarith [hr.1]) hγ.le (4*W0) N M W0 J zL zH q t hq hbound s
  simp only [hready.2.2.2.2.2,Nat.cast_zero,zero_add] at hquota
  have hquota' : P.poissonized (q*t) (FiniteKernel.eventIndicator (productiveQuotaFailure N J D)) (.inl s) ≤
      (t:ℝ)*(560*(N:ℝ)*(M:ℝ)*rho)/J := by
    apply (le_div_iff₀ (by exact_mod_cast hJ : 0 < (J:ℝ))).mpr
    nlinarith only [hquota]
  have houtput := productive_output_probability rho γ (by linarith [hr.1]) hγ.le
    (by linarith [hr.1]) N M W0 J zL zH q t hq hbound s
    (hready.2.2.1.trans (congrArg (fun w => 4*w) hstart)) hready.2.2.2.2.2
  have h := poissonized_event_cover P (q*t) (productiveBatchGoodSet N W0 J H0 L0 rho zL zH D)ᶜ
    (productiveBatchBadSets N W0 J H0 L0 rho zL zH D)
    (productive_batch_bad_cover N M W0 J H0 L0 (by omega) hH hL hw0 rho zL zH) (.inl s)
  simp [productiveBatchBadSets, Fin.sum_univ_succ] at h
  apply probability_complement_lower P (q*t) (productiveBatchGoodSet N W0 J H0 L0 rho zL zH D)
    (productiveChemicalRawError N M t+Real.exp (-(N : ℝ)/2500)+Real.exp (-(19*(N : ℝ)/500000))+(t:ℝ)*(560*(N:ℝ)*(M:ℝ)*rho)/J+Real.exp (-(W0:ℝ))) (.inl s)
  dsimp only [P,D,H0,L0] at h hpH hpL hquota' ⊢
  dsimp only at hc
  linarith only [h,hc,hd,ho,hu,hpH,hpL,hquota',houtput]

end ProductiveMemory
