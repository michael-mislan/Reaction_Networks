import proofs.FiniteReservoir.FreeTilt

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical

def FreeShortfall (V M : ℕ) (K : ℝ) : Set (BoxState V M × ℝ) :=
  {s | residenceActive V s.1.1 ∧ s.2 ≤ K}

theorem free_shortfall_split (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (K B : ℝ) (n : ℕ) (N : BoxState V M) :
    (residenceMarked V M p hV).law n
      (MarkedKernel.eventIndicator (FreeShortfall V M K)) N 0 ≤
      Real.exp ((1/1000)*(K+B/3000000)-(n:ℝ)*(33/100000000000))+
      (badOccupationKernel V M p hV).law n
        (MarkedKernel.eventIndicator {s | B ≤ s.2}) N 0 := by
  let P := residenceMarked V M p hV
  let T := freeTracked V M p hV
  have hi (X : BoxState V M × ℝ) (z : ℝ) :
      MarkedKernel.eventIndicator (FreeShortfall V M K) X.1 z ≤
        MarkedKernel.eventIndicator (FreeJointShortfall V M K B) X z+
        MarkedKernel.eventIndicator {s : (BoxState V M × ℝ) × ℝ | B ≤ s.1.2} X z := by
    by_cases h : (X.1,z) ∈ FreeShortfall V M K
    · by_cases hb : B ≤ X.2
      · have hnon := (MarkedKernel.event_bounds T (FreeJointShortfall V M K B) 0 X z).1
        simp only [MarkedKernel.law] at hnon
        unfold MarkedKernel.eventIndicator at hnon
        simp only [MarkedKernel.eventIndicator,if_pos h,Set.mem_setOf_eq,if_pos hb]
        linarith
      · have hj : (X,z) ∈ FreeJointShortfall V M K B := ⟨h.1,h.2,le_of_not_ge hb⟩
        simp only [MarkedKernel.eventIndicator,if_pos h,if_pos hj,Set.mem_setOf_eq,if_neg hb,add_zero,le_refl]
    · rw [MarkedKernel.eventIndicator,if_neg h]
      exact add_nonneg (MarkedKernel.event_bounds T _ 0 X z).1 (MarkedKernel.event_bounds T _ 0 X z).1
  have hh := T.law_mono _ _ hi n (N,0) 0
  rw [T.law_add] at hh
  have hf := tracked_free_marginal P (FiniteKernel.eventIndicator (LowFreeActive V M))
    (MarkedKernel.eventIndicator (FreeShortfall V M K)) n N 0 0
  have hb := tracked_bad_marginal P (FiniteKernel.eventIndicator (LowFreeActive V M))
    (MarkedKernel.eventIndicator {s | B ≤ s.2}) n N 0 0
  change T.law n _ (N,0) 0=_ at hf hb
  rw [hf] at hh
  have hbe : T.law n (MarkedKernel.eventIndicator {s : (BoxState V M × ℝ) × ℝ | B ≤ s.1.2}) (N,0) 0 =
      (badOccupationKernel V M p hV).law n (MarkedKernel.eventIndicator {s | B ≤ s.2}) N 0 := hb
  rw [hbe] at hh
  exact hh.trans (add_le_add (free_joint_discrete V M p hV K B n N) le_rfl)

theorem free_shortfall_after_burnin (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (K : ℝ) (m n : ℕ) (hm : 90*V ≤ m) (hn : 0 < n) (N : BoxState V M) :
    (residenceKernel V M p hV).steps m
      (fun X => (residenceMarked V M p hV).law n
        (MarkedKernel.eventIndicator (FreeShortfall V M K)) X 0) N ≤
      Real.exp ((1/1000)*(K+((n:ℝ)/100)/3000000)-(n:ℝ)*(33/100000000000))+
        100*Real.exp (-(V:ℝ)/10000000000) := by
  let R := residenceKernel V M p hV
  have hh := R.steps_mono (free_shortfall_split V M p hV K ((n:ℝ)/100) n) m N
  rw [R.steps_add,R.steps_const] at hh
  exact hh.trans (add_le_add le_rfl (bad_occupation_bound V M p hV m n hm hn N))

theorem free_shortfall_discrete (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    
    (m n : ℕ) (hm : 90*V ≤ m) (hn : 2990*V ≤ n) (N : BoxState V M) :
    (residenceKernel V M p hV).steps m
      (fun X => (residenceMarked V M p hV).law n
        (MarkedKernel.eventIndicator (FreeShortfall V M ((V:ℝ)/1080+1))) X 0) N ≤
      Real.exp (-(V:ℝ)/40000000)+100*Real.exp (-(V:ℝ)/10000000000) := by
  have hn0 : 0 < n := by omega
  have hh := free_shortfall_after_burnin V M p hV ((V:ℝ)/1080+1) m n hm hn0 N
  apply hh.trans
  apply add_le_add _ le_rfl
  apply Real.exp_le_exp.mpr
  have hn' : (2990:ℝ)*V ≤ n := by exact_mod_cast hn
  have hv' : (1000000:ℝ) ≤ V := by exact_mod_cast hlarge
  nlinarith

end
end FiniteReservoir
