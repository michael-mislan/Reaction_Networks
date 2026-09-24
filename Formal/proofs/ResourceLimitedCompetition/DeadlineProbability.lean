import proofs.ResourceLimitedCompetition.GlobalDeadline
import proofs.ResourceLimitedCompetition.PopulationMargins
import proofs.FiniteCopy.KernelExpectations

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy Set
open scoped NNReal

noncomputable local instance DeadlineProbabilityDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

def activePopulationSet (D : Finset PopulationState) : Set (StoppedPopulation D) :=
  {x | ∃ s, x=.inl s}

theorem deadline_population_nonneg (N W0 : ℕ) (D : Finset PopulationState) (x : StoppedPopulation D) :
    0 ≤ activeAncestralObservable N (deadlineValue N W0) x := by
  cases x with
  | inl s => exact deadlineValue_nonneg _ _ _ _
  | inr e => exact le_rfl

theorem active_deadline_barrier (N M : ℕ) (hN : 0 < N) (zL zH : ℝ)
    (s : ActiveState (activeDomain N M zL zH)) :
    Real.exp (-((N : ℝ)/1000)*Real.log 4) ≤
      activeAncestralObservable N (deadlineValue N (N*M)) (.inl s) := by
  have hs := activeDomain_safe N M zL zH s.val s.property
  have hm := active_founder_count_pos N M zL zH s
  have hwmin := active_membrane_lower N M zL zH s
  have hq := hs.1
  have hres := hs.2.2.1
  have hwmax : membrane s.val.live ≤ 4*(N*M) := by omega
  have hwpos : 0 < (membrane s.val.live : ℝ) := by exact_mod_cast hN.trans_le hwmin
  have hw0pos : 0 < ((N*M : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_log hwpos (by exact_mod_cast hwmax : (membrane s.val.live : ℝ) ≤ (4*(N*M) : ℕ))
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) (ne_of_gt hw0pos)] at hlog
  change Real.exp _ ≤ deadlineValue N (N*M) (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live)
  unfold deadlineValue
  rw [← Nat.cast_add,ancestral_membrane_total]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (N : ℝ)/1000)
  nlinarith only [h]

theorem poissonized_barrier {α : Type*} [Fintype α] (P : FiniteKernel α)
    (t : ℝ≥0) (A : Set α) (V : α → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hV : ∀ x, 0 ≤ V x) (hA : ∀ x ∈ A, a ≤ V x) (x : α) :
    a*P.poissonized t (FiniteKernel.eventIndicator A) x ≤ P.poissonized t V x := by
  classical
  have hn (y : α) : 0 ≤ a*FiniteKernel.eventIndicator A y := by
    unfold FiniteKernel.eventIndicator
    split_ifs <;> positivity
  have hpoint (y : α) : a*FiniteKernel.eventIndicator A y ≤ V y := by
    unfold FiniteKernel.eventIndicator
    split_ifs with hy
    · simpa only [mul_one] using hA y hy
    · simpa only [mul_zero] using hV y
  have h := P.poissonized_mono t _ _ hn hV hpoint x
  rwa [P.poissonized_scale] at h

theorem global_deadline_probability (γ : ℝ) (hγ : 0 < γ) (N M : ℕ)
    (hN : 1000 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (stoppedPopulationModel γ hγ.le (4*(N*M)) N M zL zH (activeDomain N M zL zH)).total x ≤ q)
    (hkq : (9/40000)*(N : ℝ)*γ ≤ q) (htime : (t : ℝ)=8/γ)
    (s : ActiveState (activeDomain N M zL zH)) (hstart : membrane s.val.live=N*M) :
    ((stoppedPopulationModel γ hγ.le (4*(N*M)) N M zL zH (activeDomain N M zL zH)).uniformize q hq hbound).poissonized
      (q*t) (FiniteKernel.eventIndicator (activePopulationSet (activeDomain N M zL zH))) (.inl s) ≤
      Real.exp (-(N : ℝ)/2500) := by
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

end ResourceLimitedCompetition
