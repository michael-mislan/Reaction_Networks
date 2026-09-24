import proofs.FiniteReservoir.JointTails

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped NNReal

/-- Unrounded exponent of the phase-transport certificate:
`s*(1/700-1/1000)-(12/5)*91*s^2` at `s=1/1000000`. -/
def phaseRate : ℝ := 1839/8750000000000

theorem residence_free_window_sharp (V M : ℕ) (p : Parameters M)
    (hV : 0 < (V:ℝ))
    (n : ℕ) (hn : 89*V ≤ n) (hn' : n ≤ 91*V) (N : BoxState V M) :
    (residenceKernel V M p hV).steps n
      (FiniteKernel.eventIndicator (LowFreeActive V M)) N ≤ Real.exp (-phaseRate*(V:ℝ)) := by
  let R := residenceKernel V M p hV
  have hi := R.steps_mono (residence_free_indicator V M) n N
  rw [R.steps_scale] at hi
  have ht := residence_phase_steps V M p (1/1000000) hV
    (by norm_num) (by norm_num) n N
  have hinit : residencePhaseTest V M (1/1000000) (phaseWeights (3000*(V:ℝ)) n) N ≤
      Real.exp (-(V:ℝ)/700000000) := by
    unfold residencePhaseTest
    split_ifs with hc
    · apply Real.exp_le_exp.mpr
      have hh := phase_window_stock V hV n hn hn' (boxCounts N.1)
      linarith [hc.2]
    · exact (Real.exp_pos _).le
  have hh := hi.trans (mul_le_mul_of_nonneg_left
    (ht.trans (mul_le_mul_of_nonneg_left hinit (Real.exp_pos _).le)) (Real.exp_pos _).le)
  rw [← mul_assoc,← Real.exp_add,← Real.exp_add] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hnr : (n:ℝ) ≤ 91*V := by exact_mod_cast hn'
  unfold phaseRate
  nlinarith

theorem residence_free_after_burnin_sharp (V M : ℕ) (p : Parameters M)
    (hV : 0 < (V:ℝ))
    (n : ℕ) (hn : 90*V ≤ n) (N : BoxState V M) :
    (residenceKernel V M p hV).steps n
      (FiniteKernel.eventIndicator (LowFreeActive V M)) N ≤ Real.exp (-phaseRate*(V:ℝ)) := by
  let R := residenceKernel V M p hV
  have hh := R.steps_mono
    (residence_free_window_sharp V M p hV (90*V) (by omega) (by omega)) (n-90*V) N
  rw [R.steps_const,← steps_comp] at hh
  simpa only [Nat.sub_add_cancel hn] using hh

theorem bad_occupation_bound_sharp (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (m n : ℕ) (hm : 90*V ≤ m) (hn : 0 < n) (N : BoxState V M) :
    (residenceKernel V M p hV).steps m
      (fun X => (badOccupationKernel V M p hV).law n
        (MarkedKernel.eventIndicator {s | (n:ℝ)/100 ≤ s.2}) X 0) N ≤
      100*Real.exp (-phaseRate*(V:ℝ)) := by
  have hh := occupation_markov_after_burnin (residenceMarked V M p hV)
    (residenceKernel V M p hV)
    (residence_marked_marginal V M p hV)
    (FiniteKernel.eventIndicator (LowFreeActive V M))
    (fun X => (FiniteKernel.eventIndicator_bounds _ X).1)
    (90*V) m n hm (Real.exp (-phaseRate*(V:ℝ))) ((n:ℝ)/100)
    (residence_free_after_burnin_sharp V M p hV) N
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have he : (n:ℝ)*Real.exp (-phaseRate*(V:ℝ))=
      ((n:ℝ)/100)*(100*Real.exp (-phaseRate*(V:ℝ))) := by ring
  rw [he] at hh
  exact le_of_mul_le_mul_left hh (by positivity)

theorem free_shortfall_after_burnin_sharp (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (K : ℝ) (m n : ℕ) (hm : 90*V ≤ m) (hn : 0 < n) (N : BoxState V M) :
    (residenceKernel V M p hV).steps m
      (fun X => (residenceMarked V M p hV).law n
        (MarkedKernel.eventIndicator (FreeShortfall V M K)) X 0) N ≤
      Real.exp ((1/1000)*(K+((n:ℝ)/100)/3000000)-(n:ℝ)*(33/100000000000))+
        100*Real.exp (-phaseRate*(V:ℝ)) := by
  let R := residenceKernel V M p hV
  have hh := R.steps_mono (free_shortfall_split V M p hV K ((n:ℝ)/100) n) m N
  rw [R.steps_add,R.steps_const] at hh
  exact hh.trans (add_le_add le_rfl (bad_occupation_bound_sharp V M p hV m n hm hn N))

theorem free_shortfall_discrete_sharp (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (hlarge : 1000000 ≤ V)
    (m n : ℕ) (hm : 90*V ≤ m) (hn : 2990*V ≤ n) (N : BoxState V M) :
    (residenceKernel V M p hV).steps m
      (fun X => (residenceMarked V M p hV).law n
        (MarkedKernel.eventIndicator (FreeShortfall V M ((V:ℝ)/1080+1))) X 0) N ≤
      Real.exp (-(V:ℝ)/40000000)+100*Real.exp (-phaseRate*(V:ℝ)) := by
  have hn0 : 0 < n := by omega
  have hh := free_shortfall_after_burnin_sharp V M p hV ((V:ℝ)/1080+1) m n hm hn0 N
  apply hh.trans
  apply add_le_add _ le_rfl
  apply Real.exp_le_exp.mpr
  have hn' : (2990:ℝ)*V ≤ n := by exact_mod_cast hn
  have hv' : (1000000:ℝ) ≤ V := by exact_mod_cast hlarge
  nlinarith

def sharpFreeDiscreteError (V : ℝ) : ℝ :=
  Real.exp (-V/40000000)+100*Real.exp (-phaseRate*V)

def sharpFreeCollectionError (V : ℝ) : ℝ := sharpFreeDiscreteError V+Real.exp (-V)+Real.exp (-V/200)

theorem free_precollection_bound_sharp (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (hlarge : 1000000 ≤ V)
    (n : ℕ) (hn : 2990*V ≤ n) (N : BoxState V M) :
    (residenceKernel V M p hV).poissonized ((750:ℝ≥0)*V)
      (fun X => (residenceMarked V M p hV).law n
        (MarkedKernel.eventIndicator (FreeShortfall V M ((V:ℝ)/1080+1))) X 0) N ≤
      sharpFreeDiscreteError V+Real.exp (-(V:ℝ)) := by
  let R := residenceKernel V M p hV
  let P := residenceMarked V M p hV
  let F := fun X => P.law n (MarkedKernel.eventIndicator (FreeShortfall V M ((V:ℝ)/1080+1))) X 0
  have hf (X) : 0 ≤ F X ∧ F X ≤ 1 := P.event_bounds _ n X 0
  have hh := poisson_sequence_cutoff ((750:ℝ≥0)*V) (fun m => R.steps m F N)
    (fun m => ⟨R.steps_nonneg m (fun X => (hf X).1) N,R.steps_le_one m (fun X => (hf X).2) N⟩)
    (90*V) (sharpFreeDiscreteError V) (1/2) (by unfold sharpFreeDiscreteError; positivity)
    (by norm_num) (by norm_num)
    (fun m hm => free_shortfall_discrete_sharp V M p hV hlarge m n hm hn N)
  apply hh.trans
  apply add_le_add le_rfl
  apply Real.exp_le_exp.mpr
  have hl := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<1/2 by norm_num)
  norm_num at hl
  have hm := mul_le_mul_of_nonneg_left hl hV.le
  push_cast
  nlinarith

theorem free_collection_probability_sharp (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (hlarge : 1000000 ≤ V) (N : BoxState V M) :
    freeCollectionFailure V M p hV N ≤ sharpFreeCollectionError V := by
  let R := residenceKernel V M p hV
  let P := residenceMarked V M p hV
  let F := fun n X => P.law n (MarkedKernel.eventIndicator (FreeShortfall V M ((V:ℝ)/1080+1))) X 0
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
    (sharpFreeDiscreteError V+Real.exp (-(V:ℝ))) (999/1000)
    (by unfold sharpFreeDiscreteError; positivity) (by norm_num) (by norm_num)
    (fun n hn => free_precollection_bound_sharp V M p hV hlarge n hn N)
  apply hh.trans
  unfold sharpFreeCollectionError
  apply add_le_add le_rfl
  apply Real.exp_le_exp.mpr
  have hl := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<999/1000 by norm_num)
  norm_num at hl
  have hm := mul_le_mul_of_nonneg_left hl hV.le
  push_cast
  nlinarith

/-- The free-collection failure of the joint stopped cycle with the unrounded phase rate. -/
theorem joint_free_tail_sharp (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    (N : BoxState V M) (doseU doseW : ℝ) :
    jointCycle V M p hV
      (fun X => if residenceActive V X.1.1 ∧ X.2 0 ≤ (V:ℝ)/1080+1 then 1 else 0)
      N (initialCounters doseU doseW) ≤ sharpFreeCollectionError V := by
  have he := joint_output_marginal false V M p hV
    (MarkedKernel.eventIndicator (FreeShortfall V M ((V:ℝ)/1080+1))) N doseU doseW
  dsimp [MarkedKernel.eventIndicator,FreeShortfall] at he
  convert he.le.trans ?_ using 1
  · congr 1
    funext X
    split_ifs <;> rfl
  change (materialKernel V M p hV).poissonized _
    (fun X => (residenceKernel V M p hV).poissonized _
      (fun Y => (residenceMarked V M p hV).poissonized _
        (MarkedKernel.eventIndicator (FreeShortfall V M ((V:ℝ)/1080+1))) Y 0) X) N ≤ _
  simp_rw [free_collection_nested]
  apply finite_poisson_upper_const
  · intro X
    unfold freeCollectionFailure
    apply tsum_nonneg
    intro n
    apply mul_nonneg (poissonWeight_nonneg _ _)
    exact FiniteKernel.poissonized_nonneg _ _ _
      (fun Y => ((residenceMarked V M p hV).event_bounds _ n Y 0).1) X
  · unfold sharpFreeCollectionError sharpFreeDiscreteError
    positivity
  · exact free_collection_probability_sharp V M p hV hlarge

end
end FiniteReservoir
