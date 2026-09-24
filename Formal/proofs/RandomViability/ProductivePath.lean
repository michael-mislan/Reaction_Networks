import proofs.RandomViability.ProductiveMass
import proofs.RandomViability.ProductiveSchedule

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 40000

def productivePathState {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (m i : ℕ) : Molecule n → ℕ :=
  productiveCounts N r (productiveLigations m i) (productiveExports m i)

def productivePathLabel {n : ℕ} (r : Reaction n) (m i : ℕ) : PhysicalCountChannel n :=
  if i = 0 then .inr (.inl (r,true)) else
  if productiveLigationStep m i then .inr (.inr (r,reactionProduct r,true)) else
    .inl (.inr (reactionProduct r))

theorem productive_path_initial {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (hp : N (reactionProduct r) = 0) (m : ℕ) : productivePathState N r m 0 = N := by
  simpa [productivePathState, productiveLigations, productiveExports] using
    productive_counts_initial N r hp

/-- The entire tested startup-and-export sequence is a sequence of genuine
transitions of the unbounded physical reactor. -/
theorem productive_path_next {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (m : ℕ) (hm : 0 < m) (hu : 2*m < N (reactionLeft r))
    (hw : 2*m < N (reactionRight r)) (i : ℕ) (hi : i < 3*m) :
    unboundedPhysicalNext (productivePathState N r m i) (productivePathLabel r m i) =
      productivePathState N r m (i+1) := by
  have hb := productive_schedule_bounds m i hi.le
  have hlu := hb.2.1.trans_lt hu
  have hlw := hb.2.1.trans_lt hw
  unfold productivePathState productivePathLabel
  by_cases hi0 : i=0
  · rw [if_pos hi0]
    have hs : productiveLigationStep m i := Or.inl (by omega)
    obtain ⟨hL,hE⟩ := productive_schedule_ligation m i hs
    rw [hL,hE]
    exact productive_basal_next N r huw hup hwp _ _ hlu hlw hb.1
  · rw [if_neg hi0]
    have hpos := productive_schedule_positive m i hm (Nat.pos_of_ne_zero hi0)
    by_cases hs : productiveLigationStep m i
    · rw [if_pos hs]
      obtain ⟨hL,hE⟩ := productive_schedule_ligation m i hs
      rw [hL,hE]
      exact productive_catalytic_next N r huw hup hwp _ _ hlu hlw hpos
    · rw [if_neg hs]
      obtain ⟨hL,hE⟩ := productive_schedule_export m i hs
      rw [hL,hE]
      exact productive_export_next N r hup hwp _ _ hpos

theorem productive_path_mass_le {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (hp : N (reactionProduct r)=0) (m : ℕ) (hu : 2*m ≤ N (reactionLeft r))
    (hw : 2*m ≤ N (reactionRight r)) (i : ℕ) (hi : i ≤ 3*m) :
    countMass (productivePathState N r m i) ≤ countMass N := by
  have hb := productive_schedule_bounds m i hi
  exact productive_count_mass_le N r huw hup hwp hp _ _ (hb.2.1.trans hu) (hb.2.1.trans hw) hb.1

theorem productive_path_product_counts {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (m i : ℕ) (hi : m ≤ i) :
    m ≤ productivePathState N r m i (reactionProduct r) ∧
    productivePathState N r m i (reactionProduct r) ≤ m+1 := by
  simpa [productivePathState, productiveCounts, Ne.symm hup, Ne.symm hwp] using
    productive_schedule_operating m i hi

end
end RandomViability
