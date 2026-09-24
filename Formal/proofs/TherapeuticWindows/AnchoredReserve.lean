import proofs.TherapeuticWindows.Reserve

namespace TherapeuticWindows

def anchoredWitness : ℚ :=
  278*(61/200)*120 * ∏ j ∈ Finset.range 78, (122 : ℚ)/(200-j)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem anchored_witness_certificate :
    0 < anchoredWitness ∧ anchoredWitness < 7/1000000 := by
  norm_num [anchoredWitness, Finset.prod_range_succ]

theorem original_capacity_r9 :
    20*(61/100 : ℚ)*120*(20*(61/100)/9)^10 / Nat.factorial 10 < 8452/1000000 := by
  norm_num [Nat.factorial]

theorem shared_healthy_cap :
    ((3/10 : ℚ)+29/99)/2+1/200 < 61/200 := by norm_num

end TherapeuticWindows
