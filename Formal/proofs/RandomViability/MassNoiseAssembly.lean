import proofs.RandomViability.PhysicalMassDrift
import proofs.RandomViability.SignedNonfoodInterval

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

theorem food_mass_weight_sum {n : ℕ} (hn : 2 ≤ n) :
    ∑ q : Molecule n,foodMassWeight q = 10 := by
  have hh : (∑ q ∈ binaryFood n 2,(molLength q : ℝ)) = 10 := by
    rw [Finset.sum_subtype (p := fun z => z ∈ binaryFood n 2)
      (binaryFood n 2) (fun _ => Iff.rfl)]
    have he := food_length_sum hn (fun l => (l : ℝ))
    norm_num at he
    exact he
  simpa only [binaryFood,Finset.sum_filter,foodMassWeight] using hh

def massCompensationWithinInterval {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) (s : ℝ) : ℝ :=
  if censoredNonfoodStop V T (massExitStop V) k (Preorder.frestrictLe k z) then
    censoredMassPrefix c V basal cat T z k else
    censoredMassPrefix c V basal cat T z k-physicalMassDrift c V basal cat (z k).1*s

theorem mass_interval_decomposition {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) (s : ℝ) :
    massCompensationWithinInterval c V basal cat T z k s =
      nonfoodCompensationWithinInterval c V basal cat T (massExitStop V) z k s+
      ∑ q,foodMassWeight q*coordinateCompensationWithinInterval c V basal cat q T z k s := by
  by_cases hs : censoredNonfoodStop V T (massExitStop V) k (Preorder.frestrictLe k z)
  · simpa only [massCompensationWithinInterval,nonfoodCompensationWithinInterval,
      coordinateCompensationWithinInterval,if_pos hs] using
      censored_mass_prefix_decomposition c V basal cat T z k
  · simp only [massCompensationWithinInterval,nonfoodCompensationWithinInterval,
      coordinateCompensationWithinInterval,if_neg hs]
    rw [censored_mass_prefix_decomposition,physical_mass_drift_decomposition]
    exact weighted_compensation_sum foodMassWeight
      (fun q => censoredCoordinatePrefix c V basal cat q T z k)
      (physicalCoordinateDrift c V basal cat (z k).1)
      (censoredNonfoodPrefix c V basal cat T (massExitStop V) z k)
      (physicalNonfoodDrift c V basal cat (z k).1) s

theorem mass_interval_noise_bound {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) (s ηN ηF : ℝ)
    (hN : |nonfoodCompensationWithinInterval c V basal cat T (massExitStop V) z k s| ≤ ηN)
    (hF : ∀ q : Molecule n,molLength q ≤ 2 →
      |coordinateCompensationWithinInterval c V basal cat q T z k s| ≤ ηF) :
    |massCompensationWithinInterval c V basal cat T z k s| ≤ ηN+10*ηF := by
  rw [mass_interval_decomposition]
  have hf : |∑ q : Molecule n,foodMassWeight q*
      coordinateCompensationWithinInterval c V basal cat q T z k s| ≤ 10*ηF := by
    calc
      _ ≤ ∑ q : Molecule n,|foodMassWeight q*
          coordinateCompensationWithinInterval c V basal cat q T z k s| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q : Molecule n,foodMassWeight q*ηF := by
        apply Finset.sum_le_sum
        intro q _
        by_cases hq : molLength q ≤ 2
        · rw [abs_mul,abs_of_nonneg (foodMassWeight_nonneg q)]
          exact mul_le_mul_of_nonneg_left (hF q hq) (foodMassWeight_nonneg q)
        · simp [foodMassWeight,hq]
      _ = _ := by rw [← Finset.sum_mul,food_mass_weight_sum hn]
  exact (abs_add_le _ _).trans (add_le_add hN hf)

end
end RandomViability
