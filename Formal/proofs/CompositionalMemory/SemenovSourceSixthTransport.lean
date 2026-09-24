import proofs.CompositionalMemory.SemenovSixthDrift
import proofs.CompositionalMemory.SemenovRawTransitions

namespace CompositionalMemory.Semenov
open Matrix

theorem source_raw_quadratic_increment (volume eta : ℝ) (hv : volume ≠ 0)
    (P : Matrix (Fin 8) (Fin 8) ℝ) (z : Fin 8 → ℝ) {B K : ℕ}
    (n : Fin 8 → Fin (B+1)) (c : Fin K) (r : Channel)
    (hr : 0 < reactorRate volume (some (n,c)) r) :
    matrixEnergy P ((fun j => (rawChannelNext (fun i => (n i).val) r j : ℝ)/volume)-z)/eta=
      matrixEnergy P ((fun j => ((n j).val : ℝ)/volume)-z)/eta+
        quadraticChannelDelta P ((fun j => ((n j).val : ℝ)/volume)-z) volume eta r := by
  rw [raw_channel_concentration volume hv n c r hr]
  have he : (fun j => ((n j).val : ℝ)/volume)+(1/volume) • channelJump r-z=
      ((fun j => ((n j).val : ℝ)/volume)-z)+(1/volume) • channelJump r := by abel
  rw [he]
  unfold quadraticChannelDelta
  ring

theorem source_raw_sixth_sum (volume eta : ℝ) (hv : 0 < volume)
    (P : Matrix (Fin 8) (Fin 8) ℝ) (z : Fin 8 → ℝ) {B K : ℕ}
    (n : Fin 8 → Fin (B+1)) (c : Fin K) :
    (∑ r,reactorRate volume (some (n,c)) r*
      ((matrixEnergy P ((fun j => (rawChannelNext (fun i => (n i).val) r j : ℝ)/volume)-z)/eta)^6-
       (matrixEnergy P ((fun j => ((n j).val : ℝ)/volume)-z)/eta)^6))=
      (∑ r,volume*channelIntensity (fun j => ((n j).val : ℝ)/volume) r*
        ((matrixEnergy P ((fun j => ((n j).val : ℝ)/volume)-z)/eta+
          quadraticChannelDelta P ((fun j => ((n j).val : ℝ)/volume)-z) volume eta r)^6-
         (matrixEnergy P ((fun j => ((n j).val : ℝ)/volume)-z)/eta)^6)) := by
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : 0 < reactorRate volume (some (n,c)) r
  · rw [source_raw_quadratic_increment volume eta (ne_of_gt hv) P z n c r hr,
      reactor_rate_scaling volume hv n c r]
  · have hz : reactorRate volume (some (n,c)) r=0 :=
      le_antisymm (le_of_not_gt hr) (reactorRate_nonneg volume hv.le (some (n,c)) r)
    rw [← reactor_rate_scaling volume hv n c r,hz]
    simp only [zero_mul]

end CompositionalMemory.Semenov
