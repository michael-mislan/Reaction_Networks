import proofs.MemoryPrediction.YuleAmbiguity

namespace MemoryPrediction
noncomputable section
open MeasureTheory LowFounderPrediction

/-- The detector that deletes every cell is permitted by an arbitrary-deletion
contract. It makes the complete recorded count laws identical. -/
theorem deletion_erases_source_difference :
    independentSource.map (fun _ => (0 : ℕ)) =
      sharedSource.map (fun _ => (0 : ℕ)) := by
  simp [Measure.map_const]

/-- Equal recorded laws cannot identify the distinct latent minimal cutoffs. -/
theorem deleted_count_cannot_identify_latent_cutoff
    (rule : Measure ℕ → ℕ) :
    ¬ (rule (independentSource.map (fun _ => (0 : ℕ))) = 6 ∧
      rule (sharedSource.map (fun _ => (0 : ℕ))) = 7) := by
  rw [deletion_erases_source_difference]
  omega

end
end MemoryPrediction
