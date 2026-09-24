import proofs.RandomViability.FiniteWindowGrowth
import proofs.RandomViability.PhysicalTimeCoverage

namespace RandomViability
open Filter
open scoped Topology
set_option maxHeartbeats 100000

theorem prefix_elapsed_monotone {α β : Type*} (z : ℕ → JumpState α β)
    (hh : ∀ i,0 ≤ (z (i+1)).2.2) :
    Monotone (fun k => prefixElapsed k (Preorder.frestrictLe k z)) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [prefixElapsed_restrict_succ]
  exact le_add_of_nonneg_right (hh k)

theorem prefix_elapsed_shift {α β : Type*} (z : ℕ → JumpState α β) (J K : ℕ) :
    prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) =
      prefixElapsed J (Preorder.frestrictLe J z)+∑ i : Fin K,(z (J+i+1)).2.2 := by
  induction K with
  | zero => simp only [Nat.add_zero,Fin.sum_univ_zero,add_zero]
  | succ K ih =>
    rw [Nat.add_succ,prefixElapsed_restrict_succ,ih,Fin.sum_univ_castSucc]
    change (prefixElapsed J (Preorder.frestrictLe J z)+∑ i : Fin K,(z (J+i+1)).2.2)+
      (z (J+K+1)).2.2 =
      prefixElapsed J (Preorder.frestrictLe J z)+((∑ i : Fin K,(z (J+i+1)).2.2)+(z (J+K+1)).2.2)
    ring

theorem exists_time_window_indices {α β : Type*} (z : ℕ → JumpState α β)
    (hh : ∀ i,0 ≤ (z (i+1)).2.2)
    (hd : Tendsto (fun K => prefixElapsed K (Preorder.frestrictLe K z)) atTop atTop)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∃ J K,prefixElapsed J (Preorder.frestrictLe J z) ≤ a ∧
      a < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z) ∧
      prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤ b ∧
      b < prefixElapsed (J+K+1) (Preorder.frestrictLe (J+K+1) z) := by
  obtain ⟨J,hJ,hJa⟩ := unbounded_elapsed_covers_time z hd a ha
  obtain ⟨L,hL,hLb⟩ := unbounded_elapsed_covers_time z hd b (ha.trans hab)
  have hm := prefix_elapsed_monotone z hh
  have hJL : J ≤ L := by
    by_contra h
    have he := hm (show L+1 ≤ J by omega)
    have hJ' := hJ J le_rfl
    linarith only [he,hJ',hLb,hab]
  refine ⟨J,L-J,hJ J le_rfl,hJa,?_,?_⟩
  · have he : J+(L-J) = L := by omega
    rw [he]
    exact hL L le_rfl
  · have he : J+(L-J) = L := by omega
    rw [he]
    exact hLb

theorem physical_window_duration {α β : Type*} (z : ℕ → JumpState α β)
    (J K : ℕ) (a b : ℝ) :
    windowDuration (fun i => (z (J+i+1)).2.2)
      (a-prefixElapsed J (Preorder.frestrictLe J z))
      (b-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z)) K = b-a := by
  unfold windowDuration
  rw [prefix_elapsed_shift]
  ring

end RandomViability
