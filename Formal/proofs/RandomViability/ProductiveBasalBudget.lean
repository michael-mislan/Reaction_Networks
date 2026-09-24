import proofs.RandomViability.ProductiveCurrent

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 40000

/-- Charge every basal firing its entire polymer mass in either direction.
This dominates positive basal input to any selected nonfood subnetwork. -/
def basalMassCharge {n : ℕ} (b : Unit ⊕ PhysicalCountChannel n) : ℝ :=
  match b with
  | .inr (.inr (.inl (r,_))) => molLength (reactionProduct r)
  | _ => 0

def startupOperatingMarkedSum {α β : Type*} (g : Unit ⊕ β → ℝ)
    (z : ℕ → JumpState α β) : ℝ :=
  ∑' i : ℕ, if 0 < productiveClock (fun j => (z (j+1)).2.2) (i+1) ∧
    productiveClock (fun j => (z (j+1)).2.2) (i+1) ≤ 100 then g (z (i+1)).2.1 else 0

theorem productive_before_firing_window_iff (m : ℕ) (hm : 0 < m) (τ : ℕ → ℝ)
    (hτ : ∀ i < 3*m+1, productiveWaitLower m i < τ i ∧
      τ i ≤ productiveWaitLower m i+productiveWaitWidth m)
    (hnon : ∀ i, 0 ≤ τ i) (i : ℕ) :
    (0 < productiveClock τ (i+1) ∧ productiveClock τ (i+1) ≤ 100) ↔ i < 3*m := by
  have hb := productive_clock_margins m hm τ hτ
  have hmono := productive_clock_monotone τ hnon
  have hfirst : 0 < productiveClock τ 1 := by
    have hh := (hτ 0 (by omega)).1
    have hl := productive_wait_lower_nonneg m 0
    simpa [productiveClock] using lt_of_le_of_lt hl hh
  constructor
  · intro hi
    by_contra hn
    have hh := hmono (show 3*m+1 ≤ i+1 by omega)
    linarith [hb.2.2.2,hi.2]
  · intro hi
    exact ⟨lt_of_lt_of_le hfirst (hmono (by omega)),
      (hmono (show i+1 ≤ 3*m by omega)).trans (by linarith [hb.2.2.1])⟩

theorem productive_cylinder_basal_budget {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (f : ↥(binaryFood n 2)) (m : ℕ) (hm : 0 < m)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hz : z ∈ prescribedCylinder (productivePaidState N r f m) (productivePaidLabel r f m)
      (productiveWaitLower m) (fun _ => productiveWaitWidth m) (3*m+1))
    (hnon : ∀ i, 0 ≤ (z (i+1)).2.2) :
    startupOperatingMarkedSum basalMassCharge z = molLength (reactionProduct r) := by
  have hclock (i : ℕ) := productive_before_firing_window_iff m hm _
    (productive_cylinder_waits _ _ m z hz) hnon i
  have he (i : ℕ) :
      (if 0 < productiveClock (fun j => (z (j+1)).2.2) (i+1) ∧
        productiveClock (fun j => (z (j+1)).2.2) (i+1) ≤ 100
        then basalMassCharge (z (i+1)).2.1 else 0) =
      (if i=0 then (molLength (reactionProduct r) : ℝ) else 0) := by
    simp only [hclock i]
    by_cases hi : i < 3*m
    · rw [if_pos hi]
      have hl := (hz.2 ⟨i,by omega⟩).2.1
      rw [hl]
      by_cases hi0 : i=0
      · simp [productivePaidLabel, productivePathLabel, basalMassCharge, hm, hi0]
      · by_cases hs : productiveLigationStep m i <;>
          simp [productivePaidLabel, productivePathLabel, basalMassCharge, hi, hi0, hs]
    · have hi0 : i ≠ 0 := by omega
      simp [hi,hi0]
  unfold startupOperatingMarkedSum
  rw [tsum_congr he]
  simp

end
end RandomViability
