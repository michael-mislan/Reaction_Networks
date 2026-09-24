import proofs.RandomViability.ProductivePaidPath
import proofs.RandomViability.ProductiveClockBounds

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 40000

theorem prescribed_cylinder_state {α β : Type*} (s : ℕ → α) (b : ℕ → β)
    (a d : ℕ → ℝ) (K : ℕ) (z : ℕ → JumpState α β)
    (hz : z ∈ prescribedCylinder s b a d K) (i : ℕ) (hi : i ≤ K) :
    (z i).1 = s i := by
  cases i with
  | zero => exact hz.1
  | succ i => exact (hz.2 ⟨i,by omega⟩).1

theorem productive_cylinder_waits {α β : Type*} (s : ℕ → α) (b : ℕ → β)
    (m : ℕ) (z : ℕ → JumpState α β)
    (hz : z ∈ prescribedCylinder s b (productiveWaitLower m)
      (fun _ => productiveWaitWidth m) (3*m+1)) :
    ∀ i < 3*m+1, productiveWaitLower m i < (z (i+1)).2.2 ∧
      (z (i+1)).2.2 ≤ productiveWaitLower m i+productiveWaitWidth m := by
  intro i hi
  exact (hz.2 ⟨i,hi⟩).2.2

theorem productive_clock_interval_exists (m : ℕ) (hm : 0 < m) (τ : ℕ → ℝ)
    (hτ : ∀ i < 3*m+1, productiveWaitLower m i < τ i ∧
      τ i ≤ productiveWaitLower m i+productiveWaitWidth m)
    (t : ℝ) (ht : 1 ≤ t ∧ t ≤ 100) :
    ∃ i ≤ 3*m, productiveClock τ i ≤ t ∧ t < productiveClock τ (i+1) := by
  have hb := productive_clock_margins m hm τ hτ
  have hex : ∃ j, t < productiveClock τ j := ⟨3*m+1, lt_of_le_of_lt ht.2 hb.2.2.2⟩
  have hj := Nat.find_spec hex
  have hj0 : 0 < Nat.find hex := by
    by_contra h
    have he : Nat.find hex = 0 := by omega
    rw [he] at hj
    simp only [productiveClock, Finset.range_zero, Finset.sum_empty] at hj
    linarith [ht.1]
  have hjK : Nat.find hex ≤ 3*m+1 := Nat.find_min' hex (lt_of_le_of_lt ht.2 hb.2.2.2)
  refine ⟨Nat.find hex-1,by omega,?_,?_⟩
  · exact le_of_not_gt (Nat.find_min hex (show Nat.find hex-1 < Nat.find hex by omega))
  · simpa only [Nat.sub_add_cancel (show 1 ≤ Nat.find hex by omega)] using hj

/-- Every actual population interval overlapping [1,100] has the operating
copy-number bounds, half-food resources, and the initial mass upper bound. -/
theorem productive_cylinder_residence {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (hp : N (reactionProduct r)=0) (f : ↥(binaryFood n 2))
    (V m : ℕ) (hm : 0 < m) (hmV : 4*m ≤ V)
    (hu : N (reactionLeft r)=V) (hw : N (reactionRight r)=V)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hz : z ∈ prescribedCylinder (productivePaidState N r f m) (productivePaidLabel r f m)
      (productiveWaitLower m) (fun _ => productiveWaitWidth m) (3*m+1))
    (hnon : ∀ i, 0 ≤ (z (i+1)).2.2) (i : ℕ)
    (hi : productiveClock (fun j => (z (j+1)).2.2) i ≤ 100 ∧
      1 < productiveClock (fun j => (z (j+1)).2.2) (i+1)) :
    m ≤ (z i).1 (reactionProduct r) ∧ (z i).1 (reactionProduct r) ≤ m+1 ∧
    V ≤ 2*(z i).1 (reactionLeft r) ∧ V ≤ 2*(z i).1 (reactionRight r) ∧
    countMass (z i).1 ≤ countMass N := by
  have hwindows := productive_cylinder_waits _ _ m z hz
  have hb := productive_clock_margins m hm _ hwindows
  have hmono := productive_clock_monotone _ hnon
  have him : m ≤ i := by
    by_contra h
    have hh := hmono (show i+1 ≤ m by omega)
    linarith [hb.1,hi.2]
  have hiM : i ≤ 3*m := by
    by_contra h
    have hh := hmono (show 3*m+1 ≤ i by omega)
    linarith [hb.2.2.2,hi.1]
  have hstate := prescribed_cylinder_state _ _ _ _ _ z hz i (by omega)
  rw [productivePaidState, if_pos hiM] at hstate
  rw [hstate]
  have hpcount := productive_path_product_counts N r hup hwp m i him
  have hfood := productive_path_food_floor N r huw V m i hu hw hmV hiM
  have hmass := productive_path_mass_le N r huw hup hwp hp m (by omega) (by omega) i hiM
  exact ⟨hpcount.1,hpcount.2,hfood.1,hfood.2,hmass⟩

end
end RandomViability
