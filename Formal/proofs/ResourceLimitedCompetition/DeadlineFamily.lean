import proofs.ResourceLimitedCompetition.DeadlineProbability
namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy Set
open scoped NNReal
noncomputable local instance DeadlineFamilyDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) := Classical.decEq _
theorem deadline_probability_family (γ : ℝ) (hγ : 0 < γ) (N M : ℕ)
    (hN : 1000 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (stoppedPopulationModel γ hγ.le (4*(N*M)) N M zL zH (activeDomain N M zL zH)).total x ≤ q)
    (hkq : (9/40000)*(N : ℝ)*γ ≤ q)
    (s : ActiveState (activeDomain N M zL zH)) (hstart : membrane s.val.live=N*M) :
    ((stoppedPopulationModel γ hγ.le (4*(N*M)) N M zL zH (activeDomain N M zL zH)).uniformize q hq hbound).poissonized
      (q*t) (FiniteKernel.eventIndicator (activePopulationSet (activeDomain N M zL zH))) (.inl s) ≤
      Real.exp (-((N : ℝ)/1000)*((9/40)*γ*(t : ℝ)-Real.log 4)) := by
  classical
  have hinit : activeAncestralObservable N (deadlineValue N (N*M)) (.inl s)=1 := by
    change deadlineValue N (N*M) (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live)=1
    unfold deadlineValue
    rw [← Nat.cast_add,ancestral_membrane_total,hstart]
    simp
  have hd := (stoppedPopulationModel γ hγ.le (4*(N*M)) N M zL zH (activeDomain N M zL zH)).uniformized_decay_bound
    q t hq hbound (activeAncestralObservable N (deadlineValue N (N*M)))
    (deadline_population_nonneg N (N*M) _) ((9/40000)*(N : ℝ)*γ) hkq
    (global_deadline_generator γ hγ.le N M (N*M) hN zL zH hzL hzH) (.inl s)
  rw [hinit,mul_one] at hd
  have hp := poissonized_barrier
    ((stoppedPopulationModel γ hγ.le (4*(N*M)) N M zL zH (activeDomain N M zL zH)).uniformize q hq hbound)
    (q*t) (activePopulationSet (activeDomain N M zL zH))
    (activeAncestralObservable N (deadlineValue N (N*M)))
    (Real.exp (-((N : ℝ)/1000)*Real.log 4)) (Real.exp_pos _).le
    (deadline_population_nonneg N (N*M) _)
    (by rintro x ⟨a,rfl⟩; exact active_deadline_barrier N M (by omega) zL zH a) (.inl s)
  have h := mul_le_mul_of_nonneg_left (hp.trans hd) (Real.exp_pos (((N : ℝ)/1000)*Real.log 4)).le
  have hi : Real.exp (((N : ℝ)/1000)*Real.log 4)*Real.exp (-((N : ℝ)/1000)*Real.log 4)=1 := by
    have hz : ((N : ℝ)/1000)*Real.log 4+(-((N : ℝ)/1000)*Real.log 4)=0 := by ring
    rw [← Real.exp_add,hz,Real.exp_zero]
  rw [← mul_assoc,hi,one_mul,← Real.exp_add] at h
  convert h using 1
  congr 1
  ring


end ResourceLimitedCompetition
