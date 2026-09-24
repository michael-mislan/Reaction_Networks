import proofs.CompositionalMemory.SmoothQuadraticCap

namespace CompositionalMemory

noncomputable def centeredInventory (K m0 rate t count : ℝ) : ℝ :=
  4*(count-(m0+rate*t))^2/K^2

theorem centeredInventory_nonneg (K m0 rate t count : ℝ) :
    0 ≤ centeredInventory K m0 rate t count := by
  unfold centeredInventory
  positivity

theorem centeredInventory_derivative (K m0 rate t count : ℝ) :
    HasDerivAt (fun u => centeredInventory K m0 rate u count)
      (-8*rate*(count-(m0+rate*t))/K^2) t := by
  convert (((((hasDerivAt_id t).const_mul rate).const_add m0).const_sub count).pow 2).const_mul 4 |>.div_const (K^2) using 1
  dsimp only [centeredInventory,id]
  ring

/-- Constant-rate feed contributes only its variance to the centered square. -/
theorem centeredInventory_drift (K m0 rate t count : ℝ) :
    -8*rate*(count-(m0+rate*t))/K^2+
      rate*(centeredInventory K m0 rate t (count+1)-centeredInventory K m0 rate t count)=
        4*rate/K^2 := by
  unfold centeredInventory
  ring

theorem centeredInventory_exhausted (K m0 rate t count : ℝ) (hK : 0 < K)
    (hc : K ≤ count) (hm : m0+rate*t ≤ K/2) :
    1 ≤ centeredInventory K m0 rate t count := by
  unfold centeredInventory
  apply (le_div_iff₀ (sq_pos_of_pos hK)).mpr
  have hh : 0 ≤ count-(m0+rate*t)-K/2 := by linarith
  have hj : 0 ≤ count-(m0+rate*t)+K/2 := by linarith
  nlinarith only [mul_nonneg hh hj]

theorem smoothQuadraticCap_add_cost (e b : ℝ) (he : 0 ≤ e) (hb : 0 ≤ b) :
    smoothQuadraticCap (e+b) ≤ smoothQuadraticCap e+2*b := by
  have ht := smoothQuadraticCap_tangent e (e+b)
  have hs := mul_le_mul_of_nonneg_right (smoothQuadraticSlope_bounds e he).2 hb
  nlinarith only [ht,hs]

end CompositionalMemory
