import proofs.RAF1519.Refinement.MarkMoments

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators

def markRate (m : PhysicalMark) (d : ℝ) (c : State) : ℝ :=
  match m with
  | .inventory => ProductiveRecovery.inventory (free c)
  | .freeX => c 2
  | .foodU => 1
  | .foodW => 1
  | .service => service d (1/100) (1/100) c

theorem physical_mark_drift {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V : ℝ) (hV : V ≠ 0) (N : MolecularState n) (i : Fin n) (m : PhysicalMark) :
    (∑ a, molecularRate r d k V N a*markIncrement V i m N a) =
      markRate m (d i) (concentration V (fun s => N (i,s))) := by
  have hm := graph_normalized_mark_moment r d k V hV N i m 0
  simp only [Nat.zero_add,pow_one] at hm
  rw [hm]
  cases m
  all_goals dsimp [localMarkedMoment,markRate,service,ProductiveRecovery.inventory,free,concentration]
  all_goals try field_simp
  all_goals ring

end
end RAF1519.Refinement
