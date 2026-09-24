import proofs.FiniteReservoir.ResidenceFree
import proofs.FiniteCopyReactor.Occupation

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped BigOperators

/-- Only literal free-X washout is counted. Internal or service labels give zero. -/
def freeWashoutMark : CompetitionChannel → ℝ
  | .inl j => if j=14 then 1 else 0
  | .inr _ => 0

theorem free_washout_intensity (N : Counts) (V r alpha beta : ℝ) :
    (∑ j,internalRate N V r alpha beta j*freeWashoutMark j)=(N 2:ℝ) := by
  simp [Fintype.sum_sum_type,internalRate,freeWashoutMark,countRate]

def residenceMarked (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     :
    MarkedKernel (BoxState V M) (Option CompetitionChannel) :=
  (residenceModel V M p hV).withMarks freeWashoutMark
    (3000*(V:ℝ)) (by positivity) (residence_total V M p hV)

theorem residence_marked_marginal (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : BoxState V M → ℝ) (N : BoxState V M) (z : ℝ) :
    (residenceMarked V M p hV).step (fun X _ => f X) N z=
      (residenceKernel V M p hV).step f N :=
  (residenceModel V M p hV).marked_step_marginal freeWashoutMark
    (3000*(V:ℝ)) (by positivity) (residence_total V M p hV) f N z

def badOccupationKernel (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     :=
  stateMarks (residenceMarked V M p hV)
    (fun N _ => FiniteKernel.eventIndicator (LowFreeActive V M) N)

theorem bad_occupation_bound (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (m n : ℕ) (hm : 90*V ≤ m) (hn : 0 < n) (N : BoxState V M) :
    (residenceKernel V M p hV).steps m
      (fun X => (badOccupationKernel V M p hV).law n
        (MarkedKernel.eventIndicator {s | (n:ℝ)/100 ≤ s.2}) X 0) N ≤
      100*Real.exp (-(V:ℝ)/10000000000) := by
  have hh := occupation_markov_after_burnin (residenceMarked V M p hV)
    (residenceKernel V M p hV)
    (residence_marked_marginal V M p hV)
    (FiniteKernel.eventIndicator (LowFreeActive V M))
    (fun X => (FiniteKernel.eventIndicator_bounds _ X).1)
    (90*V) m n hm (Real.exp (-(V:ℝ)/10000000000)) ((n:ℝ)/100)
    (residence_free_after_burnin V M p hV) N
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have he : (n:ℝ)*Real.exp (-(V:ℝ)/10000000000)=
      ((n:ℝ)/100)*(100*Real.exp (-(V:ℝ)/10000000000)) := by ring
  rw [he] at hh
  exact le_of_mul_le_mul_left hh (by positivity)

end
end FiniteReservoir
