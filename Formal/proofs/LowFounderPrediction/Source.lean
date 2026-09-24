import proofs.InheritedCellAssay.FiniteClockProjection
import proofs.FiniteCopyReactor.StoppedAgreement
import proofs.CompositionalMemory.FiniteTimeDependentCertificate

namespace LowFounderPrediction
noncomputable section
open Classical FiniteCopy FiniteCopyReactor CompositionalMemory

abbrev State := ℕ × ℕ

structure Rates where
  bS : ℝ
  dS : ℝ
  qS : ℝ
  bR : ℝ
  dR : ℝ
  qR : ℝ
  bS_nonneg : 0 ≤ bS
  dS_nonneg : 0 ≤ dS
  qS_nonneg : 0 ≤ qS
  bR_nonneg : 0 ≤ bR
  dR_nonneg : 0 ≤ dR
  qR_nonneg : 0 ≤ qR

/-- Original physical per-day L1 rate neighborhoods. -/
def RateBall (a : Rates) : Prop :=
  |a.bS|+|a.dS-3/10|+|a.qS-1/1000| ≤ 1/2000 ∧
  |a.bR-1/10|+|a.dR|+|a.qR-1/100000| ≤ 1/2000

def next (x : State) (b : Fin 7) : State :=
  if b.val = 0 then (x.1+1,x.2)
  else if b.val = 1 then (x.1-1,x.2)
  else if b.val = 2 then (x.1-1,x.2+1)
  else if b.val = 3 then (x.1,x.2+1)
  else if b.val = 4 then (x.1,x.2-1)
  else if b.val = 5 then (x.1+1,x.2-1)
  else x

def rate (a : Rates) (x : State) (b : Fin 7) : ℝ :=
  if b.val = 0 then a.bS*x.1
  else if b.val = 1 then a.dS*x.1
  else if b.val = 2 then a.qS*x.1
  else if b.val = 3 then a.bR*x.2
  else if b.val = 4 then a.dR*x.2
  else if b.val = 5 then a.qR*x.2
  else 1

theorem rate_nonneg (a : Rates) (x : State) (b : Fin 7) : 0 ≤ rate a x b := by
  have := a.bS_nonneg; have := a.dS_nonneg; have := a.qS_nonneg
  have := a.bR_nonneg; have := a.dR_nonneg; have := a.qR_nonneg
  unfold rate
  split_ifs <;> positivity

theorem total_eq (a : Rates) (x : State) :
    (∑ b, rate a x b) = (a.bS+a.dS+a.qS)*x.1+(a.bR+a.dR+a.qR)*x.2+1 := by
  simp [Fin.sum_univ_succ, rate]
  ring

theorem total_pos (a : Rates) (x : State) : 0 < ∑ b, rate a x b := by
  rw [total_eq]
  have := a.bS_nonneg; have := a.dS_nonneg; have := a.qS_nonneg
  have := a.bR_nonneg; have := a.dR_nonneg; have := a.qR_nonneg
  positivity

/-- Six retained states: empty, S, R, RR, RRR, cemetery. -/
def observe (x : State) : Fin 6 :=
  if x = (0,0) then 0 else if x = (1,0) then 1
  else if x = (0,1) then 2 else if x = (0,2) then 3
  else if x = (0,3) then 4 else 5

def repr (n : Fin 6) : State :=
  if n.val = 0 then (0,0) else if n.val = 1 then (1,0)
  else if n.val = 2 then (0,1) else if n.val = 3 then (0,2)
  else if n.val = 4 then (0,3) else (2,0)

def live : Set State := {x | observe x ≠ 5}

theorem repr_observe (x : State) (hx : x ∈ live) : repr (observe x) = x := by
  simp only [live, Set.mem_setOf_eq] at hx
  unfold observe at *
  split_ifs at * <;> simp_all [repr]

def killed (a : Rates) : FiniteJumpModel (Fin 6) (Fin 7) where
  next n b := if n.val = 5 then 5 else observe (next (repr n) b)
  rate n b := if n.val = 5 then 0 else rate a (repr n) b
  nonneg n b := by split_ifs; exact le_rfl; exact rate_nonneg a _ _

def clockRate (a : Rates) : ℝ :=
  2+3*(a.bS+a.dS+a.qS+a.bR+a.dR+a.qR)

theorem clock_pos (a : Rates) : 0 < clockRate a := by
  have := a.bS_nonneg; have := a.dS_nonneg; have := a.qS_nonneg
  have := a.bR_nonneg; have := a.dR_nonneg; have := a.qR_nonneg
  unfold clockRate
  positivity

theorem repr_bound (a : Rates) (n : Fin 6) :
    (∑ b, rate a (repr n) b) ≤ clockRate a := by
  have := a.bS_nonneg; have := a.dS_nonneg; have := a.qS_nonneg
  have := a.bR_nonneg; have := a.dR_nonneg; have := a.qR_nonneg
  rw [total_eq]
  fin_cases n <;> norm_num [repr, clockRate] <;> linarith

theorem live_bound (a : Rates) (x : State) (hx : x ∈ live) :
    (∑ b, rate a x b) ≤ clockRate a := by
  rw [← repr_observe x hx]
  exact repr_bound a _

theorem killed_bound (a : Rates) (n : Fin 6) :
    (killed a).total n ≤ clockRate a := by
  by_cases hn : n = 5
  · simp [FiniteJumpModel.total, killed, hn, (clock_pos a).le]
  · have hn' : n.val ≠ 5 := fun h => hn (Fin.ext h)
    simpa [FiniteJumpModel.total, killed, hn'] using repr_bound a n

def stopped (a : Rates) :=
  stoppedClockKernel live next (rate a) (rate_nonneg a) (clockRate a) (clock_pos a)
    (live_bound a)

theorem step_projection (a : Rates) (g : Fin 6 → ℝ) (x : State) :
    (∑ b, (stopped a).prob x b * g (observe ((stopped a).next x b))) =
      ((killed a).uniformize (clockRate a) (clock_pos a) (killed_bound a)).step g
        (observe x) := by
  rw [FiniteJumpModel.uniformize_step]
  by_cases hx : x ∈ live
  · have hneq : (observe x).val ≠ 5 := fun h => hx (Fin.ext h)
    simp [stopped, stoppedClockKernel, boundedClockKernel, stoppedRate, hx,
      Fintype.sum_option, FiniteJumpModel.generator, killed, hneq, repr_observe x hx]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  · have ho : observe x = 5 := by simpa [live] using hx
    simp [stopped, stoppedClockKernel, boundedClockKernel, stoppedRate, hx,
      Fintype.sum_option, ho, FiniteJumpModel.generator, killed]

end
end LowFounderPrediction
