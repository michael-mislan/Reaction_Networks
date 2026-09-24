import proofs.FiniteCopyReactor.FreeShortfall
import proofs.FiniteCopyReactor.PoissonSequence

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

def freeDiscreteError (V : ℝ) : ℝ :=
  Real.exp (-V/40000000)+100*Real.exp (-V/10000000000)

def freeCollectionError (V : ℝ) : ℝ := freeDiscreteError V+Real.exp (-V)+Real.exp (-V/200)

/-- Independent Poisson clocks for the actual quarter-unit precollection
continuation and one-unit marked collection. The intermediate state is retained. -/
def freeCollectionFailure (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) : ℝ :=
  ∑' n,poissonWeight ((3000:ℝ≥0)*V) n*
    (residenceKernel V r d hV (by linarith) hr' hd hd').poissonized ((750:ℝ≥0)*V)
      (fun X => (residenceMarked V r d hV hr hr' hd hd').law n
        (MarkedKernel.eventIndicator (FreeShortfall V ((V:ℝ)/1080+1))) X 0) N

theorem free_precollection_bound (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (n : ℕ) (hn : 2990*V ≤ n) (N : BoxCounts V) :
    (residenceKernel V r d hV (by linarith) hr' hd hd').poissonized ((750:ℝ≥0)*V)
      (fun X => (residenceMarked V r d hV hr hr' hd hd').law n
        (MarkedKernel.eventIndicator (FreeShortfall V ((V:ℝ)/1080+1))) X 0) N ≤
      freeDiscreteError V+Real.exp (-(V:ℝ)) := by
  let R := residenceKernel V r d hV (by linarith) hr' hd hd'
  let P := residenceMarked V r d hV hr hr' hd hd'
  let F := fun X => P.law n (MarkedKernel.eventIndicator (FreeShortfall V ((V:ℝ)/1080+1))) X 0
  have hf (X) : 0 ≤ F X ∧ F X ≤ 1 := P.event_bounds _ n X 0
  have hh := poisson_sequence_cutoff ((750:ℝ≥0)*V) (fun m => R.steps m F N)
    (fun m => ⟨R.steps_nonneg m (fun X => (hf X).1) N,R.steps_le_one m (fun X => (hf X).2) N⟩)
    (90*V) (freeDiscreteError V) (1/2) (by unfold freeDiscreteError; positivity) (by norm_num) (by norm_num)
    (fun m hm => free_shortfall_discrete V r d hV hlarge hr hr' hd hd' m n hm hn N)
  apply hh.trans
  apply add_le_add le_rfl
  apply Real.exp_le_exp.mpr
  have hl := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<1/2 by norm_num)
  norm_num at hl
  have hm := mul_le_mul_of_nonneg_left hl hV.le
  push_cast
  nlinarith

theorem free_collection_probability (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) :
    freeCollectionFailure V r d hV hr hr' hd hd' N ≤ freeCollectionError V := by
  let R := residenceKernel V r d hV (by linarith) hr' hd hd'
  let P := residenceMarked V r d hV hr hr' hd hd'
  let F := fun n X => P.law n (MarkedKernel.eventIndicator (FreeShortfall V ((V:ℝ)/1080+1))) X 0
  have hf (n X) : 0 ≤ F n X ∧ F n X ≤ 1 := P.event_bounds _ n X 0
  have hu (n) : 0 ≤ R.poissonized ((750:ℝ≥0)*V) (F n) N ∧
      R.poissonized ((750:ℝ≥0)*V) (F n) N ≤ 1 := by
    constructor
    · exact R.poissonized_nonneg _ _ (fun X => (hf n X).1) N
    · have hh := R.poissonized_mono ((750:ℝ≥0)*V) (F n) (fun _ => 1)
        (fun X => (hf n X).1) (fun _ => by norm_num) (fun X => (hf n X).2) N
      simpa only [R.poissonized_const] using hh
  have hh := poisson_sequence_cutoff ((3000:ℝ≥0)*V)
    (fun n => R.poissonized ((750:ℝ≥0)*V) (F n) N) hu (2990*V)
    (freeDiscreteError V+Real.exp (-(V:ℝ))) (999/1000)
    (by unfold freeDiscreteError; positivity) (by norm_num) (by norm_num)
    (fun n hn => free_precollection_bound V r d hV hlarge hr hr' hd hd' n hn N)
  apply hh.trans
  unfold freeCollectionError
  apply add_le_add le_rfl
  apply Real.exp_le_exp.mpr
  have hl := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<999/1000 by norm_num)
  norm_num at hl
  have hm := mul_le_mul_of_nonneg_left hl hV.le
  push_cast
  nlinarith

end
end FiniteCopyReactor
