import proofs.RandomViability.ProductiveCandidate
import proofs.RandomViability.ProductivePaidPath
import proofs.RandomViability.ProductiveWindowCost

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

def productiveEpsilon : ℝ := 1/500000000

def productiveFeed {n : ℕ} (hn : 4 ≤ n) : ↥(binaryFood n 2) :=
  ⟨reactionLeft (productiveReaction hn),(productive_reaction_food hn).1⟩

def productiveCylinderEvent {n : ℕ} (hn : 4 ≤ n) (V : ℕ) :
    Set (ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :=
  prescribedCylinder
    (productivePaidState (foodOnlyCounts n V) (productiveReaction hn) (productiveFeed hn) ((V+9)/10))
    (productivePaidLabel (productiveReaction hn) (productiveFeed hn) ((V+9)/10))
    (productiveWaitLower ((V+9)/10)) (fun _ => productiveWaitWidth ((V+9)/10))
    (3*((V+9)/10)+1)

def productiveBeta (V : ℕ) : ℝ := productivePathBudget (V : ℝ) ((V+9)/10) productiveEpsilon

theorem productiveBeta_pos (V : ℕ) (hV : 40 ≤ V) : 0 < productiveBeta V := by
  exact productive_path_budget_pos _ _ _ (productive_volume_rounding V hV).1
    (by norm_num [productiveEpsilon])

variable {n : ℕ} [mCh : MeasurableSpace (PhysicalCountChannel n)]
  [sCh : MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Concrete food-only, full-network productive path lower probability.
Only one source incidence is assumed; every other catalyst row is unrestricted. -/
theorem concrete_productive_probability_lower (hn : 4 ≤ n) (V : ℕ) (hV : 40 ≤ V)
    (c : SourceMoleculeFibreConfig n)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r, productiveEpsilon ≤ (basal r : ℝ) ∧ (basal r : ℝ) ≤ 4*productiveEpsilon)
    (hc : ∀ r z, 4 ≤ (cat r z : ℝ) ∧ (cat r z : ℝ) ≤ 16)
    (hsel : productiveReaction hn ∈ c (reactionProduct (productiveReaction hn))) :
    ENNReal.ofReal (productiveBeta V) ≤
      physicalTrajectoryLaw (by omega) c (V : NNReal) 1
        (by exact_mod_cast (show 0 < V by omega)) (by norm_num) basal cat (foodOnlyCounts n V)
        (productiveCylinderEvent hn V) := by
  let r := productiveReaction hn
  let N := foodOnlyCounts n V
  let m := (V+9)/10
  let f := productiveFeed hn
  have hd := productive_reaction_distinct hn
  have hinit := productive_initial_counts hn V
  have hround := productive_volume_rounding V hV
  have hbasal : ∀ r, (basal r : ℝ) ≤ 1 := by
    intro r
    calc
      _ ≤ 4*productiveEpsilon := (hb r).2
      _ ≤ 1 := by norm_num [productiveEpsilon]
  have hpath := physical_productive_cylinder_lower (by omega) c N r
    hd.1 hd.2.1 hd.2.2 hinit.2.2 f V m (by omega) hround.1 hround.2.1
    hinit.1 hinit.2.1 (food_only_count_mass_le (by omega) V) basal cat
    productiveEpsilon (by norm_num [productiveEpsilon]) (by norm_num [productiveEpsilon])
    (hb r).1 (hc r (reactionProduct r)).1 hsel hbasal (fun r z => (hc r z).2)
    (productiveWaitLower m) (fun _ => productiveWaitWidth m)
    (fun i _ => productive_wait_lower_nonneg m i)
    (fun _ _ => (productive_wait_width_pos m hround.1).le)
  exact (productive_window_product_lower (V : ℝ) m productiveEpsilon (by positivity)
    hround.1 (by norm_num [productiveEpsilon])).trans hpath

end
end RandomViability
