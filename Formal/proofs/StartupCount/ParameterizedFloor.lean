import proofs.StartupCount.DyadicCertificate

namespace StartupCount
noncomputable section
set_option maxHeartbeats 40000

theorem count_rounding_bounds_small_volume (V : ℝ) (hV : 10000000000000000000000 ≤ V) :
    10 ≤ countCut V ∧ (countCut V : ℝ) ≤ V/2000000000000000000 ∧
    100 ≤ dyadicIndex V ∧ 10*dyadicIndex V ≤ countCut V-stockThreshold V-1 ∧
    stockThreshold V+1 ≤ 100*(dyadicIndex V+1) ∧
    (countCut V : ℝ) ≤ V/100000000000000000 := by
  have hv : 0 ≤ V := by linarith
  have hm := Nat.floor_le (show 0 ≤ V/2000000000000000000 by positivity)
  have hm' := Nat.lt_floor_add_one (V/2000000000000000000)
  have hh := Nat.ceil_lt_add_one (show 0 ≤ V/3000000000000000000 by positivity)
  have hN := Nat.floor_le (show 0 ≤ V/100000000000000000000 by positivity)
  have hN' := Nat.lt_floor_add_one (V/100000000000000000000)
  change (countCut V : ℝ) ≤ _ at hm
  change V/2000000000000000000 < (countCut V : ℝ)+1 at hm'
  change (stockThreshold V : ℝ) < V/3000000000000000000+1 at hh
  change (dyadicIndex V : ℝ) ≤ _ at hN
  change V/100000000000000000000 < (dyadicIndex V : ℝ)+1 at hN'
  have hm10 : 10 ≤ countCut V := by
    apply (Nat.le_floor_iff (show 0 ≤ V/2000000000000000000 by positivity)).mpr
    norm_num
    linarith
  have hN100 : 100 ≤ dyadicIndex V := by
    apply (Nat.le_floor_iff (show 0 ≤ V/100000000000000000000 by positivity)).mpr
    norm_num
    linarith
  have hgap : 10*dyadicIndex V+stockThreshold V+1 ≤ countCut V := by
    have he : (10 : ℝ)*dyadicIndex V+stockThreshold V+1 ≤ countCut V := by linarith
    exact_mod_cast he
  have hhN : stockThreshold V+1 ≤ 100*(dyadicIndex V+1) := by
    have he : (stockThreshold V : ℝ)+1 ≤ 100*((dyadicIndex V : ℝ)+1) := by linarith
    exact_mod_cast he
  exact ⟨hm10,hm,hN100,by omega,hhN,by linarith⟩


end
end StartupCount

