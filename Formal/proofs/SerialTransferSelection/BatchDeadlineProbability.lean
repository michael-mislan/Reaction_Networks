import proofs.SerialTransferSelection.BatchDeadlineGenerator
import proofs.ResourceLimitedCompetition.DeadlineProbability

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal
noncomputable local instance DeadlineDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) := Classical.decEq _

theorem phase_active_deadline_barrier (N M W0 : ℕ) (hN : 0 < N) (hM : 0 < M) (zL zH : ℝ)
    (s : ActiveState (phaseActiveDomain N M W0 zL zH)) :
    Real.exp (-((N : ℝ)/1000)*Real.log 4) ≤
      activeAncestralObservable N (deadlineValue N W0) (.inl s) := by
  have hs := phaseActiveDomain_safe N M W0 zL zH s.val s.property
  have hm := phase_active_W0_pos N M W0 zL zH s
  have hwmin := phase_active_membrane_lower N M W0 hM zL zH s
  have hq := hs.1
  have hres := hs.2.2.1
  have hwmax : membrane s.val.live ≤ 4*W0 := by omega
  have hwpos : 0 < (membrane s.val.live : ℝ) := by exact_mod_cast hN.trans_le hwmin
  have hw0pos : 0 < (W0 : ℝ) := by positivity
  have hlog := Real.log_le_log hwpos (by exact_mod_cast hwmax : (membrane s.val.live : ℝ) ≤ (4*W0 : ℕ))
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) (ne_of_gt hw0pos)] at hlog
  change Real.exp _ ≤ deadlineValue N W0 (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live)
  unfold deadlineValue
  rw [← Nat.cast_add,ancestral_membrane_total]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (N : ℝ)/1000)
  nlinarith only [h]

theorem phase_global_deadline_probability (γ : ℝ) (hγ : 0 < γ) (N M W0 : ℕ)
    (hN : 1000 ≤ N) (hM : 0 < M) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (phaseStoppedModel γ hγ.le (4*W0) N W0 zL zH (phaseActiveDomain N M W0 zL zH)).total x ≤ q)
    (hkq : (9/40000)*(N : ℝ)*γ ≤ q) (htime : (t : ℝ)=8/γ)
    (s : ActiveState (phaseActiveDomain N M W0 zL zH)) (hstart : membrane s.val.live=W0) :
    ((phaseStoppedModel γ hγ.le (4*W0) N W0 zL zH (phaseActiveDomain N M W0 zL zH)).uniformize q hq hbound).poissonized
      (q*t) (FiniteKernel.eventIndicator (activePopulationSet (phaseActiveDomain N M W0 zL zH))) (.inl s) ≤
      Real.exp (-(N : ℝ)/2500) := by
  classical
  have hinit : activeAncestralObservable N (deadlineValue N W0) (.inl s)=1 := by
    change deadlineValue N W0 (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live)=1
    unfold deadlineValue
    rw [← Nat.cast_add,ancestral_membrane_total,hstart]
    simp
  have hd := (phaseStoppedModel γ hγ.le (4*W0) N W0 zL zH (phaseActiveDomain N M W0 zL zH)).uniformized_decay_bound
    q t hq hbound (activeAncestralObservable N (deadlineValue N W0))
    (deadline_population_nonneg N W0 _) ((9/40000)*(N : ℝ)*γ) hkq
    (phase_global_deadline_generator γ hγ.le N M W0 hN hM zL zH hzL hzH) (.inl s)
  rw [hinit,mul_one] at hd
  have hp := poissonized_barrier
    ((phaseStoppedModel γ hγ.le (4*W0) N W0 zL zH (phaseActiveDomain N M W0 zL zH)).uniformize q hq hbound)
    (q*t) (activePopulationSet (phaseActiveDomain N M W0 zL zH))
    (activeAncestralObservable N (deadlineValue N W0))
    (Real.exp (-((N : ℝ)/1000)*Real.log 4)) (Real.exp_pos _).le
    (deadline_population_nonneg N W0 _)
    (by rintro x ⟨a,rfl⟩; exact phase_active_deadline_barrier N M W0 (by omega) hM zL zH a) (.inl s)
  have ht : -((9/40000)*(N : ℝ)*γ)*(t : ℝ)=-(9/5000)*(N : ℝ) := by
    rw [htime]
    field_simp [ne_of_gt hγ]
    norm_num
  rw [ht] at hd
  have h := mul_le_mul_of_nonneg_left (hp.trans hd) (Real.exp_pos (((N : ℝ)/1000)*Real.log 4)).le
  have hi : Real.exp (((N : ℝ)/1000)*Real.log 4)*Real.exp (-((N : ℝ)/1000)*Real.log 4)=1 := by
    have hz : ((N : ℝ)/1000)*Real.log 4+(-((N : ℝ)/1000)*Real.log 4)=0 := by ring
    rw [← Real.exp_add,hz,Real.exp_zero]
  rw [← mul_assoc,hi,one_mul,← Real.exp_add] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  linarith only [population_deadline_margin (N : ℝ) (Nat.cast_nonneg _)]

end SerialTransferSelection
