import proofs.RandomViability.ProductiveRealized

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

/-- A pathwise operating criterion: chronological residence, signed catalytic
output, export, unchanged endpoint stock, and a conservative basal budget.
All quantifiers are over jump indices, so the event is countably measurable. -/
def ProductiveOperation {n : ℕ} (r : Reaction n) (V m : ℕ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  (∀ i, 0 ≤ (z (i+1)).2.2) ∧
  (∀ i, productiveClock (fun j => (z (j+1)).2.2) i ≤ 100 ∧
      1 < productiveClock (fun j => (z (j+1)).2.2) (i+1) →
    V ≤ 20*(z i).1 (reactionProduct r) ∧ 5*(z i).1 (reactionProduct r) ≤ V ∧
    V ≤ 2*(z i).1 (reactionLeft r) ∧ V ≤ 2*(z i).1 (reactionRight r) ∧
    countMass (z i).1 ≤ 10*V) ∧
  (∃ i j, (productiveClock (fun k => (z (k+1)).2.2) i ≤ 1 ∧
      1 < productiveClock (fun k => (z (k+1)).2.2) (i+1)) ∧
    (productiveClock (fun k => (z (k+1)).2.2) j ≤ 100 ∧
      100 < productiveClock (fun k => (z (k+1)).2.2) (j+1)) ∧
    (z i).1 (reactionProduct r) = m ∧ (z j).1 (reactionProduct r) = m) ∧
  operatingMarkedSum (targetSignedCatalytic r) z = m ∧
  operatingMarkedSum (targetProductExport r) z = m ∧
  startupOperatingMarkedSum basalMassCharge z ≤ (4*(m : ℝ))/4

/-- Every realized concrete cylinder meets the complete operating criterion. -/
theorem productive_realized_operation {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 40 ≤ V)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hz : z ∈ productiveRealizedEvent hn V) :
    ProductiveOperation (productiveReaction hn) V ((V+9)/10) z := by
  let r := productiveReaction hn
  let N := foodOnlyCounts n V
  let m := (V+9)/10
  let f := productiveFeed hn
  have hd := productive_reaction_distinct hn
  have hi := productive_initial_counts hn V
  have hr := productive_volume_rounding V hV
  have hz' : z ∈ prescribedCylinder (productivePaidState N r f m)
      (productivePaidLabel r f m) (productiveWaitLower m)
      (fun _ => productiveWaitWidth m) (3*m+1) := hz.2
  have hend := productive_cylinder_endpoints N r hd.2.1 hd.2.2 f m hr.1 z hz'
  have hout := productive_cylinder_current N r f m hr.1 z hz' hz.1
  have hbasal := productive_cylinder_basal_budget N r f m hr.1 z hz' hz.1
  have hlength : molLength (reactionProduct r) = 4 := (productive_reaction_lengths hn).2.2
  refine ⟨hz.1,?_,⟨m,3*m,hend⟩,hout.1,hout.2,?_⟩
  · intro i hclock
    have hb := productive_cylinder_residence N r hd.1 hd.2.1 hd.2.2 hi.2.2 f V m
      hr.1 hr.2.1 hi.1 hi.2.1 z hz' hz.1 i hclock
    have hmass := food_only_count_mass_le (show 2 ≤ n by omega) V
    refine ⟨?_,?_,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.trans hmass⟩
    · change V ≤ 20*(z i).1 (reactionProduct r)
      omega
    · change 5*(z i).1 (reactionProduct r) ≤ V
      omega
  · rw [hbasal,hlength]
    have hm : 4 ≤ m := by dsimp [m]; omega
    norm_num
    exact hm

end
end RandomViability
