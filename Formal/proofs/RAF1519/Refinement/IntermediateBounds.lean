import proofs.RAF1519.Refinement.Source

namespace RAF1519.Refinement
noncomputable section

/-- The whole parameter interval, not just its rational endpoints. -/
theorem forcing_gap (d : ℝ) (hd' : d ≤ 1/25) :
    d*(1+1/100)*(8800000121/8000000000) <
      (1+d*(1+1/100)/(1/100))*(9/1000) := by
  linarith

theorem kappa_bounds (d : ℝ) (hd : 1/50 ≤ d) (hd' : d ≤ 1/25) :
    151/50 ≤ 1+d*(1+1/100)/(1/100) ∧
    1+d*(1+1/100)/(1/100) ≤ 126/25 := by
  constructor <;> linarith

theorem forcing_bound (c : State) (hc : ∀ i, 0 ≤ c i) (hu : c 0 ≤ 11/10)
    (hw : c 1 ≤ 11/10) (hx : c 2 ≤ 11/10) :
    forcing (1/100) c ≤ 8800000121/8000000000 := by
  have hp := mul_le_mul hu hw (hc 1) (by norm_num : (0:ℝ) ≤ 11/10)
  dsimp [forcing]
  linarith

theorem intermediate_inward (r d : ℝ) (c : State) (hd : 1/50 ≤ d)
    (hd' : d ≤ 1/25) (hf : forcing (1/100) c ≤ 8800000121/8000000000)
    (hb : 9/1000 ≤ c 6) : field r d (1/100) (1/100) c 6 < 0 := by
  rw [intermediate_filter r d (1/100) (1/100) c (by norm_num)]
  have hk := kappa_bounds d hd hd'
  have hg := forcing_gap d hd'
  have hm := mul_le_mul_of_nonneg_left hf (show 0 ≤ d*(1+1/100) by linarith)
  have hn := mul_le_mul_of_nonneg_left hb (show 0 ≤ 1+d*(1+1/100)/(1/100) by linarith [hk.1])
  linarith

theorem noise_amplification (D : ℝ) (hD : 0 ≤ D) :
    (1/(100000*(1+D)))*(1+((126/25)+2*D)/(151/50)) < 3/100000 := by
  have hden : 0 < 100000*(1+D) := by positivity
  calc
    _ = (1+((126/25)+2*D)/(151/50))/(100000*(1+D)) := by ring
    _ < 3/100000 := (div_lt_iff₀ hden).2 (by linarith)

theorem free_material_from_augmented (c : State)
    (hA : 1-1/25-18/100000 ≤ materialA c)
    (hB : 1-1/25-18/100000 ≤ materialB c) (hb : c 6 ≤ 1104/100000) :
    94878/100000 ≤ ProductiveRecovery.A (free c) ∧
    94878/100000 ≤ ProductiveRecovery.B (free c) := by
  dsimp [materialA,materialB] at hA hB
  constructor <;> linarith

theorem intermediate_return_margin :
    (9/1000:ℝ)+(201/100000)/125000+3/100000 < 904/100000 ∧
    (904/100000:ℝ) < 1101/100000 := by norm_num

theorem service_rate_bound (d : ℝ) (c : State) (hd' : d ≤ 1/25)
    (hc : ∀ i, 0 ≤ c i) (hx : c 2 ≤ 11/10) (hb : c 6 ≤ 1104/100000) :
    service d (1/100) (1/100) c ≤ 448816/10000000 := by
  have hs : 0 ≤ (1+1/100)*c 2+c 6 := by linarith [hc 2,hc 6]
  have hm := mul_le_mul_of_nonneg_right hd' hs
  have hh : (1+1/100)*c 2+c 6 ≤ (1+1/100)*(11/10)+1104/100000 := by linarith
  dsimp [service]
  nlinarith
end
end RAF1519.Refinement
