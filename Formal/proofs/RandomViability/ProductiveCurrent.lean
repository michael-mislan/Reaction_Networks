import proofs.RandomViability.ProductiveResidence
import proofs.RandomViability.ProductiveFiringTimes

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 40000

def targetSignedCatalytic {n : ℕ} (r : Reaction n) (b : Unit ⊕ PhysicalCountChannel n) : ℝ :=
  if b = .inr (.inr (.inr (r,reactionProduct r,true))) then 1 else
  if b = .inr (.inr (.inr (r,reactionProduct r,false))) then -1 else 0

def targetProductExport {n : ℕ} (r : Reaction n) (b : Unit ⊕ PhysicalCountChannel n) : ℝ :=
  if b = .inr (.inl (.inr (reactionProduct r))) then 1 else 0

def operatingMarkedSum {α β : Type*} (g : Unit ⊕ β → ℝ) (z : ℕ → JumpState α β) : ℝ :=
  ∑' i : ℕ, if 1 < productiveClock (fun j => (z (j+1)).2.2) (i+1) ∧
    productiveClock (fun j => (z (j+1)).2.2) (i+1) ≤ 100 then g (z (i+1)).2.1 else 0

/-- Full chronological signed catalytic count and export count on (1,100].
The signed observable includes reverse catalysis with weight minus one. -/
theorem productive_cylinder_current {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (f : ↥(binaryFood n 2)) (m : ℕ) (hm : 0 < m)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hz : z ∈ prescribedCylinder (productivePaidState N r f m) (productivePaidLabel r f m)
      (productiveWaitLower m) (fun _ => productiveWaitWidth m) (3*m+1))
    (hnon : ∀ i, 0 ≤ (z (i+1)).2.2) :
    operatingMarkedSum (targetSignedCatalytic r) z = m ∧
    operatingMarkedSum (targetProductExport r) z = m := by
  have hwindows := productive_cylinder_waits _ _ m z hz
  have hclock (i : ℕ) := productive_firing_window_iff m hm _ hwindows hnon i
  have hs (i : ℕ) :
      (if 1 < productiveClock (fun j => (z (j+1)).2.2) (i+1) ∧
        productiveClock (fun j => (z (j+1)).2.2) (i+1) ≤ 100
        then targetSignedCatalytic r (z (i+1)).2.1 else 0) =
      (if m ≤ i ∧ i < 3*m then (if (i-m)%2=0 then (1 : ℝ) else 0) else 0) := by
    simp only [hclock i]
    by_cases hi : m ≤ i ∧ i < 3*m
    · rw [if_pos hi, if_pos hi]
      have hlabel := (hz.2 ⟨i,by omega⟩).2.1
      rw [hlabel]
      have hi0 : i ≠ 0 := by omega
      have him : ¬ i < m := by omega
      by_cases hp : (i-m)%2=0 <;>
        simp [targetSignedCatalytic, productivePaidLabel, productivePathLabel,
          productiveLigationStep, hi.2, hi0, him, hp]
    · rw [if_neg hi,if_neg hi]
  have he (i : ℕ) :
      (if 1 < productiveClock (fun j => (z (j+1)).2.2) (i+1) ∧
        productiveClock (fun j => (z (j+1)).2.2) (i+1) ≤ 100
        then targetProductExport r (z (i+1)).2.1 else 0) =
      (if m ≤ i ∧ i < 3*m then (if (i-m)%2=1 then (1 : ℝ) else 0) else 0) := by
    simp only [hclock i]
    by_cases hi : m ≤ i ∧ i < 3*m
    · rw [if_pos hi,if_pos hi]
      have hlabel := (hz.2 ⟨i,by omega⟩).2.1
      rw [hlabel]
      have hi0 : i ≠ 0 := by omega
      have him : ¬ i < m := by omega
      by_cases hp : (i-m)%2=0
      · simp [targetProductExport, productivePaidLabel, productivePathLabel,
          productiveLigationStep, hi.2, hi0, him, hp]
      · have hp1 : (i-m)%2=1 := by omega
        simp [targetProductExport, productivePaidLabel, productivePathLabel,
          productiveLigationStep, hi.2, hi0, him, hp1]
    · rw [if_neg hi,if_neg hi]
  constructor
  · exact (tsum_congr hs).trans (productive_operating_parity_count m 0 (by omega))
  · exact (tsum_congr he).trans (productive_operating_parity_count m 1 (by omega))

end
end RandomViability
