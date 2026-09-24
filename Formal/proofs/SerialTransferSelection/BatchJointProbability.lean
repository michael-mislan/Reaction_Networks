import proofs.SerialTransferSelection.BatchJointEvent

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal
noncomputable local instance JointProbabilityDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) := Classical.decEq _

theorem phase_source_batch_joint_return (N M W0 : ℕ) (hN : 1000 ≤ N) (hM : 0 < M) (hW : W0 ≤ 2*N*M)
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
    let P := (phaseStoppedModel γ hγ.le (4*W0) N W0 zL zH
      (phaseActiveDomain N M W0 zL zH)).uniformize q hq hbound
    1-(phaseChemicalRawError N M t+Real.exp (-(N : ℝ)/2500)+Real.exp (-(19*(N : ℝ)/500000))) ≤
      P.poissonized (q*t) (FiniteKernel.eventIndicator
        (phaseBatchGoodSet N W0 (ancestralMembrane true s.val.live)
          (ancestralMembrane false s.val.live) zL zH (phaseActiveDomain N M W0 zL zH))) (.inl s) := by
  classical
  dsimp only
  let D := phaseActiveDomain N M W0 zL zH
  let P := (phaseStoppedModel γ hγ.le (4*W0) N W0 zL zH D).uniformize q hq hbound
  let H0 := ancestralMembrane true s.val.live
  let L0 := ancestralMembrane false s.val.live
  have hw0 : H0+L0=W0 := (ancestral_membrane_total s.val.live).trans hstart
  have hc := phase_global_chemical_probability N M W0 (by omega) hW hlarge zL zH γ
    hzL hzH hsL hsH hγ.le hγmax q t hq hbound s hready
  have hd := phase_global_deadline_probability γ hγ N M W0 hN hM zL zH hzL hzH
    q t hq hbound hkq htime s hstart
  have ho := phase_global_odds_probability γ hγ.le (4*W0) N M W0 hN zL zH hzL hzH
    q t hq hbound s hH hL
  have hu := phase_unflagged_probability γ hγ.le N M W0 (by omega) hW zL zH hzL hzH
    q t hq hbound s
  have hpH := phase_ancestry_below_probability γ hγ.le (4*W0) N W0 H0 zL zH D true
    q t hq hbound (.inl s) (le_refl _)
  have hpL := phase_ancestry_below_probability γ hγ.le (4*W0) N W0 L0 zL zH D false
    q t hq hbound (.inl s) (le_refl _)
  have h := poissonized_event_cover P (q*t) (phaseBatchGoodSet N W0 H0 L0 zL zH D)ᶜ
    (phaseBatchBadSets N W0 H0 L0 zL zH D)
    (phase_batch_bad_cover N M W0 H0 L0 (by omega) hH hL hw0 zL zH) (.inl s)
  simp [phaseBatchBadSets, Fin.sum_univ_succ] at h
  apply probability_complement_lower P (q*t) (phaseBatchGoodSet N W0 H0 L0 zL zH D)
    (phaseChemicalRawError N M t+Real.exp (-(N : ℝ)/2500)+Real.exp (-(19*(N : ℝ)/500000))) (.inl s)
  dsimp only [P,D,H0,L0] at h hpH hpL ⊢
  dsimp only at hc
  linarith only [h,hc,hd,ho,hu,hpH,hpL]

end SerialTransferSelection
