import proofs.CompositionalMemory.SemenovEncoding
import proofs.CompositionalMemory.SemenovSourceTransport

namespace CompositionalMemory.Semenov

def channelFeedIncrement : Channel → ℕ
  | Sum.inr (Sum.inl _) => 1
  | _ => 0

theorem total_feed_rate (volume : ℝ) {B K : ℕ} (n : Fin 8 → Fin (B+1)) (c : Fin K) :
    (∑ j,reactorRate volume (some (n,c)) (Sum.inr (Sum.inl j)))=
      volume*(1/500)*(15231/100000 : ℝ) := by
  simp only [reactorRate,← Finset.mul_sum,feed_total_nominal]

/-- Exact variance drift of the raw feed count; absorption is handled by the
combined-energy comparison, not by this identity. -/
theorem raw_inventory_generator (volume m0 t : ℝ) {B K : ℕ}
    (n : Fin 8 → Fin (B+1)) (c : Fin K) :
    -8*(volume*(1/500)*(15231/100000))*(c.val-(m0+volume*(1/500)*(15231/100000)*t))/(K : ℝ)^2+
      (∑ r,reactorRate volume (some (n,c)) r*
        (centeredInventory K m0 (volume*(1/500)*(15231/100000)) t
          ((c.val : ℝ)+(channelFeedIncrement r : ℝ))-
         centeredInventory K m0 (volume*(1/500)*(15231/100000)) t c.val))=
      4*(volume*(1/500)*(15231/100000))/(K : ℝ)^2 := by
  simp only [Fintype.sum_sum_type,channelFeedIncrement,Nat.cast_zero,Nat.cast_one,
    add_zero,sub_self,mul_zero,Finset.sum_const_zero,zero_add]
  rw [← Finset.sum_mul,total_feed_rate]
  exact centeredInventory_drift (K : ℝ) m0 (volume*(1/500)*(15231/100000)) t c.val

end CompositionalMemory.Semenov
