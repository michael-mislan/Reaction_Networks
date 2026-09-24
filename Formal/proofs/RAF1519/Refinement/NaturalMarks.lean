import proofs.RAF1519.Refinement.MarkPath

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 30000

def naturalMark {n : ℕ} (i : Fin n) (m : PhysicalMark) (a : Unit ⊕ CountChannel n) : ℕ :=
  a.elim (fun _ => 0) (physicalMarkReward i m)

def naturalMarkPrefix {n : ℕ} (i : Fin n) (m : PhysicalMark)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (K : ℕ) : ℕ :=
  ∑ j ∈ Finset.range K, naturalMark i m (z (j+1)).2.1

theorem rewardPrefix_natural {n : ℕ} (V : ℝ) (i : Fin n) (m : PhysicalMark)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (K : ℕ) :
    rewardPrefix (markIncrement V i m) z K=(naturalMarkPrefix i m z K:ℝ)/V := by
  unfold rewardPrefix naturalMarkPrefix
  rw [Nat.cast_sum,Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (z (j+1)).2.1.elim (fun _ => (0:ℝ)) (markIncrement V i m (z j).1)) K]
  apply Finset.sum_congr rfl
  intro j _
  cases (z (j+1)).2.1 <;> simp only [Sum.elim_inl,Sum.elim_inr,naturalMark,markIncrement,Nat.cast_zero,zero_div]

theorem naturalMarkPrefix_mono {n : ℕ} (i : Fin n) (m : PhysicalMark)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) : Monotone (naturalMarkPrefix i m z) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (fun _ _ _ => Nat.zero_le _)

theorem countPathIndex_mono_on {n : ℕ}
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ j, 0 ≤ (z (j+1)).2.2)
    (K : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hK : b < prefixElapsed K (Preorder.frestrictLe K z)) : countPathIndex z a ≤ countPathIndex z b := by
  have hia := countPathIndex_spec z hh K a ha (hab.trans_lt hK)
  have hib := countPathIndex_spec z hh K b (ha.trans hab) hK
  by_contra hn
  have hl : countPathIndex z b+1 ≤ countPathIndex z a := by omega
  have hm := holdingClock_monotone (fun j => (z (j+1)).2.2) hh hl
  rw [holdingClock_succ] at hm
  change prefixElapsed (countPathIndex z b) (Preorder.frestrictLe (countPathIndex z b) z)+
    (z (countPathIndex z b+1)).2.2 ≤ prefixElapsed (countPathIndex z a) (Preorder.frestrictLe (countPathIndex z a) z) at hm
  linarith [hia.2.1,hib.2.2]

def naturalMarkedWindow {n : ℕ} (i : Fin n) (m : PhysicalMark)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (a b : ℝ) : ℕ :=
  naturalMarkPrefix i m z (countPathIndex z b)-naturalMarkPrefix i m z (countPathIndex z a)

theorem markedWindow_natural {n : ℕ} (V : ℝ) (i : Fin n) (m : PhysicalMark)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ j, 0 ≤ (z (j+1)).2.2)
    (K : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hK : b < prefixElapsed K (Preorder.frestrictLe K z)) :
    markPath V i m z b-markPath V i m z a=(naturalMarkedWindow i m z a b:ℝ)/V := by
  have hm := naturalMarkPrefix_mono i m z (countPathIndex_mono_on z hh K a b ha hab hK)
  simp only [markPath,rewardPrefix_natural,naturalMarkedWindow,Nat.cast_sub hm,sub_div]

end
end RAF1519.Refinement
