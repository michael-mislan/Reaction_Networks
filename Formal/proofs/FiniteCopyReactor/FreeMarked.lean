import proofs.FiniteCopyReactor.ResidenceFree
import proofs.FiniteCopyReactor.Occupation

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

/-- Only literal free-X washout is counted. Internal or service labels give zero. -/
def freeWashoutMark : CompetitionChannel → ℝ
  | .inl j => if j=14 then 1 else 0
  | .inr _ => 0

theorem free_washout_intensity (N : Counts) (V r d : ℝ) :
    (∑ j,competitionRate N V (1/500000000) (1/10) r d j*freeWashoutMark j)=(N 2:ℝ) := by
  simp [Fintype.sum_sum_type,competitionRate,freeWashoutMark,countRate]

def residenceMarked (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    MarkedKernel (BoxCounts V) (Option CompetitionChannel) :=
  (residenceModel V r d hV (by linarith) hd).withMarks freeWashoutMark
    (3000*(V:ℝ)) (by positivity) (residence_total_bound V r d hV (by linarith) hr' hd hd')

theorem residence_marked_marginal (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V → ℝ) (N : BoxCounts V) (z : ℝ) :
    (residenceMarked V r d hV hr hr' hd hd').step (fun X _ => f X) N z=
      (residenceKernel V r d hV (by linarith) hr' hd hd').step f N :=
  (residenceModel V r d hV (by linarith) hd).marked_step_marginal freeWashoutMark
    (3000*(V:ℝ)) (by positivity) (residence_total_bound V r d hV (by linarith) hr' hd hd') f N z

def badOccupationKernel (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :=
  stateMarks (residenceMarked V r d hV hr hr' hd hd')
    (fun N _ => FiniteKernel.eventIndicator (LowFreeActive V) N)

theorem bad_occupation_bound (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (m n : ℕ) (hm : 90*V ≤ m) (hn : 0 < n) (N : BoxCounts V) :
    (residenceKernel V r d hV (by linarith) hr' hd hd').steps m
      (fun X => (badOccupationKernel V r d hV hr hr' hd hd').law n
        (MarkedKernel.eventIndicator {s | (n:ℝ)/100 ≤ s.2}) X 0) N ≤
      100*Real.exp (-(V:ℝ)/10000000000) := by
  have hh := occupation_markov_after_burnin (residenceMarked V r d hV hr hr' hd hd')
    (residenceKernel V r d hV (by linarith) hr' hd hd')
    (residence_marked_marginal V r d hV hr hr' hd hd')
    (FiniteKernel.eventIndicator (LowFreeActive V))
    (fun X => (FiniteKernel.eventIndicator_bounds _ X).1)
    (90*V) m n hm (Real.exp (-(V:ℝ)/10000000000)) ((n:ℝ)/100)
    (residence_free_after_burnin V r d hV hr hr' hd hd') N
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have he : (n:ℝ)*Real.exp (-(V:ℝ)/10000000000)=
      ((n:ℝ)/100)*(100*Real.exp (-(V:ℝ)/10000000000)) := by ring
  rw [he] at hh
  exact le_of_mul_le_mul_left hh (by positivity)

end
end FiniteCopyReactor
