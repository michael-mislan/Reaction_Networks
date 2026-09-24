import proofs.ProductiveMemory.ExtractionDeadlineGenerator
import proofs.ResourceLimitedCompetition.DeadlineProbability

namespace ProductiveMemory
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal
noncomputable local instance ProductiveDeadlineDecidableEq (D : Finset ProductiveState) : DecidableEq (ProductiveStopped D) := Classical.decEq _

def productiveActiveSet (D : Finset ProductiveState) : Set (ProductiveStopped D) :=
  {x | ∃ a, x=.inl a}

theorem productive_deadline_nonneg (N W0 : ℕ) (D : Finset ProductiveState)
    (x : ProductiveStopped D) : 0 ≤ productiveActiveAncestralObservable N (deadlineValue N W0) x := by
  cases x with
  | inl s => exact deadlineValue_nonneg _ _ _ _
  | inr e => exact le_rfl

theorem productive_active_deadline_barrier (N M W0 J : ℕ) (hN : 0 < N) (hM : 0 < M) (rho zL zH : ℝ)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) :
    Real.exp (-((N : ℝ)/1000)*Real.log 4) ≤
      productiveActiveAncestralObservable N (deadlineValue N W0) (.inl s) := by
  have hs := productive_active_safe N M W0 J rho zL zH s.val s.property
  have hm := productive_active_W0_pos N M W0 J rho zL zH s
  have hwmin := productive_active_membrane_lower N M W0 J hM rho zL zH s
  have hq := hs.1
  have hres := hs.2.2.1
  have hwmax : membrane s.val.population.live ≤ 4*W0 := by omega
  have hwpos : 0 < (membrane s.val.population.live : ℝ) := by exact_mod_cast hN.trans_le hwmin
  have hw0pos : 0 < (W0 : ℝ) := by positivity
  have hlog := Real.log_le_log hwpos (by exact_mod_cast hwmax : (membrane s.val.population.live : ℝ) ≤ (4*W0 : ℕ))
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) (ne_of_gt hw0pos)] at hlog
  change Real.exp _ ≤ deadlineValue N W0 (ancestralMembrane true s.val.population.live) (ancestralMembrane false s.val.population.live)
  unfold deadlineValue
  rw [← Nat.cast_add,ancestral_membrane_total]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (N : ℝ)/1000)
  nlinarith only [h]

theorem productive_global_deadline_probability (γ : ℝ) (hγ : 0 < γ) (N M W0 J : ℕ)
    (hN : 1000 ≤ N) (hM : 0 < M) (rho zL zH : ℝ)
    (hrho : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (productiveStoppedModel rho γ (by linarith [hrho.1]) hγ.le (4*W0) N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).total x ≤ q)
    (hkq : (9/40000)*(N : ℝ)*γ ≤ q) (htime : (t : ℝ)=8/γ)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) (hstart : membrane s.val.population.live=W0) :
    ((productiveStoppedModel rho γ (by linarith [hrho.1]) hγ.le (4*W0) N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).uniformize q hq hbound).poissonized
      (q*t) (FiniteKernel.eventIndicator (productiveActiveSet (productiveActiveDomain N M W0 J rho zL zH))) (.inl s) ≤
      Real.exp (-(N : ℝ)/2500) := by
  classical
  have hinit : productiveActiveAncestralObservable N (deadlineValue N W0) (.inl s)=1 := by
    change deadlineValue N W0 (ancestralMembrane true s.val.population.live) (ancestralMembrane false s.val.population.live)=1
    unfold deadlineValue
    rw [← Nat.cast_add,ancestral_membrane_total,hstart]
    simp
  have hd := (productiveStoppedModel rho γ (by linarith [hrho.1]) hγ.le (4*W0) N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).uniformized_decay_bound
    q t hq hbound (productiveActiveAncestralObservable N (deadlineValue N W0))
    (productive_deadline_nonneg N W0 _) ((9/40000)*(N : ℝ)*γ) hkq
    (productive_global_deadline_generator γ hγ.le N M W0 J hN hM rho zL zH hrho hzL hzH) (.inl s)
  rw [hinit,mul_one] at hd
  have hp := poissonized_barrier
    ((productiveStoppedModel rho γ (by linarith [hrho.1]) hγ.le (4*W0) N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).uniformize q hq hbound)
    (q*t) (productiveActiveSet (productiveActiveDomain N M W0 J rho zL zH))
    (productiveActiveAncestralObservable N (deadlineValue N W0))
    (Real.exp (-((N : ℝ)/1000)*Real.log 4)) (Real.exp_pos _).le
    (productive_deadline_nonneg N W0 _)
    (by rintro x ⟨a,rfl⟩; exact productive_active_deadline_barrier N M W0 J (by omega) hM rho zL zH a) (.inl s)
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

end ProductiveMemory
