import proofs.RandomViability.ProductiveResidence

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

/-- The populations at the two observation endpoints both contain exactly m
copies of the product. The inequalities also identify their actual holding intervals. -/
theorem productive_cylinder_endpoints {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (f : ↥(binaryFood n 2)) (m : ℕ) (hm : 0 < m)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hz : z ∈ prescribedCylinder (productivePaidState N r f m) (productivePaidLabel r f m)
      (productiveWaitLower m) (fun _ => productiveWaitWidth m) (3*m+1)) :
    (productiveClock (fun j => (z (j+1)).2.2) m ≤ 1 ∧
      1 < productiveClock (fun j => (z (j+1)).2.2) (m+1)) ∧
    (productiveClock (fun j => (z (j+1)).2.2) (3*m) ≤ 100 ∧
      100 < productiveClock (fun j => (z (j+1)).2.2) (3*m+1)) ∧
    (z m).1 (reactionProduct r) = m ∧ (z (3*m)).1 (reactionProduct r) = m := by
  have hb := productive_clock_margins m hm _ (productive_cylinder_waits _ _ m z hz)
  have hs := prescribed_cylinder_state _ _ _ _ _ z hz m (by omega)
  have he := prescribed_cylinder_state _ _ _ _ _ z hz (3*m) (by omega)
  have hc := productive_schedule_endpoints m
  refine ⟨⟨by linarith [hb.1],hb.2.1⟩,⟨by linarith [hb.2.2.1],hb.2.2.2⟩,?_,?_⟩
  · rw [hs]
    simp [productivePaidState, show m ≤ 3*m by omega, productivePathState,
      productiveCounts, Ne.symm hup, Ne.symm hwp, hc.2.2.1, hc.2.2.2.1]
  · rw [he]
    simp [productivePaidState, productivePathState, productiveCounts,
      Ne.symm hup, Ne.symm hwp, hc.2.2.2.2.1, hc.2.2.2.2.2]
    omega

end
end RandomViability
