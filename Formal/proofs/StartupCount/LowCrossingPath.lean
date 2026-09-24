import proofs.StartupCount.PrefixReadiness
import proofs.StartupCount.CrossingRate

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability Set
noncomputable section
set_option maxHeartbeats 50000
variable {α β : Type*}

def crossingAt (guard : α → Prop) (count : α → ℕ) (h : ℕ) (a b : ℝ) (k : ℕ) :
    Set (ℕ → JumpState α β) :=
  {z | readyPrefix guard k (Preorder.frestrictLe k z) (jumpElapsed z (k+1)) ∧
    a < jumpElapsed z (k+1) ∧ jumpElapsed z (k+1) ≤ b ∧
    h ≤ count (z k).1 ∧ count (z (k+1)).1 < h}

theorem jumpElapsed_mono (z : ℕ → JumpState α β) (hw : ∀ i,0 ≤ (z (i+1)).2.2) :
    Monotone (jumpElapsed z) := by
  apply monotone_nat_of_le_succ
  intro k
  unfold jumpElapsed
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (hw k)

/-- A later low holding interval has either an initial low holding interval
or a marked downward crossing inside the original operating window. -/
theorem low_interval_requires_crossing (guard : α → Prop) (count : α → ℕ)
    (h : ℕ) (hh : 0 < h) (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b)
    (z : ℕ → JumpState α β) (hw : ∀ i,0 ≤ (z (i+1)).2.2)
    (hstart : ∃ J,(∀ j ≤ J,jumpElapsed z j ≤ a) ∧ a < jumpElapsed z (J+1))
    (hlow : z ∈ guardedLowEvent guard count (h-1) t) :
    z ∈ guardedLowEvent guard count (h-1) a ∨ ∃ k,z ∈ crossingAt guard count h a b k := by
  obtain ⟨J,hJa,hJa'⟩ := hstart
  obtain ⟨K,hguard,hpre,hpost,hcount⟩ := hlow
  have hJK : J ≤ K := by
    by_contra hnot
    have he := hJa (K+1) (by omega)
    linarith
  by_cases hj : count (z J).1 < h
  · left
    exact ⟨J,fun j hj => hguard j (hj.trans hJK),hJa,hJa',by omega⟩
  · right
    have hend : count (z (J+(K-J))).1 < h := by
      rw [Nat.add_sub_of_le hJK]
      omega
    obtain ⟨i,hi,hbefore,hafter⟩ := low_after_start_requires_crossing
      (fun j => count (z j).1) J (K-J) h (Nat.le_of_not_lt hj) hend
    have hm := jumpElapsed_mono z hw
    have hidx : J+i+1 ≤ K := by omega
    refine ⟨J+i,?_,?_,?_,hbefore,hafter⟩
    · apply (readyPrefix_restrict guard (J+i) z _).mpr
      exact ⟨fun j hj => hguard j (by omega),fun j hj => hm (by omega)⟩
    · exact hJa'.trans_le (hm (by omega))
    · exact (hpre (J+i+1) hidx).trans htb

end
end StartupCount
