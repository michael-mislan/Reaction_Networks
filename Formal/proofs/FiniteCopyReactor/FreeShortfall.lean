import proofs.FiniteCopyReactor.FreeTilt

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

def FreeShortfall (V : ℕ) (K : ℝ) : Set (BoxCounts V × ℝ) :=
  {s | residenceActive V s.1 ∧ s.2 ≤ K}

theorem free_shortfall_split (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (K B : ℝ) (n : ℕ) (N : BoxCounts V) :
    (residenceMarked V r d hV hr hr' hd hd').law n
      (MarkedKernel.eventIndicator (FreeShortfall V K)) N 0 ≤
      Real.exp ((1/1000)*(K+B/3000000)-(n:ℝ)*(33/100000000000))+
      (badOccupationKernel V r d hV hr hr' hd hd').law n
        (MarkedKernel.eventIndicator {s | B ≤ s.2}) N 0 := by
  let P := residenceMarked V r d hV hr hr' hd hd'
  let T := freeTracked V r d hV hr hr' hd hd'
  have hi (X : BoxCounts V × ℝ) (z : ℝ) :
      MarkedKernel.eventIndicator (FreeShortfall V K) X.1 z ≤
        MarkedKernel.eventIndicator (FreeJointShortfall V K B) X z+
        MarkedKernel.eventIndicator {s : (BoxCounts V × ℝ) × ℝ | B ≤ s.1.2} X z := by
    by_cases h : (X.1,z) ∈ FreeShortfall V K
    · by_cases hb : B ≤ X.2
      · have hnon := (MarkedKernel.event_bounds T (FreeJointShortfall V K B) 0 X z).1
        simp only [MarkedKernel.law] at hnon
        unfold MarkedKernel.eventIndicator at hnon
        simp only [MarkedKernel.eventIndicator,if_pos h,Set.mem_setOf_eq,if_pos hb]
        linarith
      · have hj : (X,z) ∈ FreeJointShortfall V K B := ⟨h.1,h.2,le_of_not_ge hb⟩
        simp only [MarkedKernel.eventIndicator,if_pos h,if_pos hj,Set.mem_setOf_eq,if_neg hb,add_zero,le_refl]
    · rw [MarkedKernel.eventIndicator,if_neg h]
      exact add_nonneg (MarkedKernel.event_bounds T _ 0 X z).1 (MarkedKernel.event_bounds T _ 0 X z).1
  have hh := T.law_mono _ _ hi n (N,0) 0
  rw [T.law_add] at hh
  have hf := tracked_free_marginal P (FiniteKernel.eventIndicator (LowFreeActive V))
    (MarkedKernel.eventIndicator (FreeShortfall V K)) n N 0 0
  have hb := tracked_bad_marginal P (FiniteKernel.eventIndicator (LowFreeActive V))
    (MarkedKernel.eventIndicator {s | B ≤ s.2}) n N 0 0
  change T.law n _ (N,0) 0=_ at hf hb
  rw [hf] at hh
  have hbe : T.law n (MarkedKernel.eventIndicator {s : (BoxCounts V × ℝ) × ℝ | B ≤ s.1.2}) (N,0) 0 =
      (badOccupationKernel V r d hV hr hr' hd hd').law n (MarkedKernel.eventIndicator {s | B ≤ s.2}) N 0 := hb
  rw [hbe] at hh
  exact hh.trans (add_le_add (free_joint_discrete V r d hV hr hr' hd hd' K B n N) le_rfl)

theorem free_shortfall_after_burnin (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (K : ℝ) (m n : ℕ) (hm : 90*V ≤ m) (hn : 0 < n) (N : BoxCounts V) :
    (residenceKernel V r d hV (by linarith) hr' hd hd').steps m
      (fun X => (residenceMarked V r d hV hr hr' hd hd').law n
        (MarkedKernel.eventIndicator (FreeShortfall V K)) X 0) N ≤
      Real.exp ((1/1000)*(K+((n:ℝ)/100)/3000000)-(n:ℝ)*(33/100000000000))+
        100*Real.exp (-(V:ℝ)/10000000000) := by
  let R := residenceKernel V r d hV (by linarith) hr' hd hd'
  have hh := R.steps_mono (free_shortfall_split V r d hV hr hr' hd hd' K ((n:ℝ)/100) n) m N
  rw [R.steps_add,R.steps_const] at hh
  exact hh.trans (add_le_add le_rfl (bad_occupation_bound V r d hV hr hr' hd hd' m n hm hn N))

theorem free_shortfall_discrete (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (m n : ℕ) (hm : 90*V ≤ m) (hn : 2990*V ≤ n) (N : BoxCounts V) :
    (residenceKernel V r d hV (by linarith) hr' hd hd').steps m
      (fun X => (residenceMarked V r d hV hr hr' hd hd').law n
        (MarkedKernel.eventIndicator (FreeShortfall V ((V:ℝ)/1080+1))) X 0) N ≤
      Real.exp (-(V:ℝ)/40000000)+100*Real.exp (-(V:ℝ)/10000000000) := by
  have hn0 : 0 < n := by omega
  have hh := free_shortfall_after_burnin V r d hV hr hr' hd hd' ((V:ℝ)/1080+1) m n hm hn0 N
  apply hh.trans
  apply add_le_add _ le_rfl
  apply Real.exp_le_exp.mpr
  have hn' : (2990:ℝ)*V ≤ n := by exact_mod_cast hn
  have hv' : (1000000:ℝ) ≤ V := by exact_mod_cast hlarge
  nlinarith

end
end FiniteCopyReactor
