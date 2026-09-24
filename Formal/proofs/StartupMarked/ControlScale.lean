import proofs.StartupMarked.RetainedControls

namespace StartupMarked
noncomputable section
set_option maxHeartbeats 50000

theorem nonfood_exponent_at_scale (n V d : ℝ) (hn : 0 < n) (hV : 10000000000000*n ≤ V)
    (hd : 0 < d) (hnum : 79*4*(96011*200+d) < d^2*10000000000000) :
    79 < nonfoodExponent n V d := by
  apply (lt_div_iff₀ (show 0 < 4*n*(96011*200+d) by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left hV (sq_nonneg d)
  have hs := mul_lt_mul_of_pos_right hnum hn
  nlinarith only [hh,hs]

theorem coordinate_exponent_at_scale (V d : ℝ) (hV : 1000000000000000000000000 ≤ V)
    (hd : 0 < d) (hnum : 79*4*(96000*200+2*d) < d^2*1000000000000000000000000) :
    79 < coordinateExponent V d := by
  apply (lt_div_iff₀ (show 0 < 4*(96000*200+2*d) by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left hV (sq_nonneg d)
  nlinarith only [hh,hnum]

theorem retained_exponents (n V : ℝ) (hn : 4 ≤ n)
    (hV : 1000000000000000000000000 ≤ V) (hVn : 10000000000000*n ≤ V) :
    79 < nonfoodExponent n V (99/800) ∧
    79 < coordinateExponent V (99/8000) ∧
    79 < coordinateExponent V (99/10000000) ∧
    79 < nonfoodExponent n V (99/4000) ∧
    79 < nonfoodExponent n V (99/100) := by
  exact ⟨nonfood_exponent_at_scale n V _ (by linarith) hVn (by norm_num) (by norm_num),
    coordinate_exponent_at_scale V _ hV (by norm_num) (by norm_num),
    coordinate_exponent_at_scale V _ hV (by norm_num) (by norm_num),
    nonfood_exponent_at_scale n V _ (by linarith) hVn (by norm_num) (by norm_num),
    nonfood_exponent_at_scale n V _ (by linarith) hVn (by norm_num) (by norm_num)⟩

theorem retained_jump_margins (n V : ℝ)
    (hV : 1000000000000000000000000 ≤ V) (hVn : 10000000000000*n ≤ V) :
    99/800+n/V ≤ 1/8 ∧ 99/8000+2/V ≤ 1/80 ∧
    99/10000000+2/V ≤ 1/100000 ∧ 99/4000+n/V ≤ 1/40 ∧ 99/100+n/V ≤ 1 := by
  have hv : 0 < V := by linarith
  have hnV : n/V ≤ 1/10000000000000 := (div_le_iff₀ hv).mpr (by linarith)
  have h2V : 2/V ≤ 2/1000000000000000000000000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hV
  constructor
  · linarith only [hnV]
  constructor
  · linarith only [h2V]
  constructor
  · linarith only [h2V]
  constructor <;> linarith only [hnV]

end
end StartupMarked
