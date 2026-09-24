import proofs.ThreeSitePhosphorylation.FrequencyData

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 1000000

def frequencySlope (t : ℝ) : ℝ :=
    (5728/6045:ℝ)*t^7 +
    (45363713206799695617936821/632555519470875000000:ℝ)*t^6 +
    (8362584637034098682974692474934473341/24139134823678875000000000000:ℝ)*t^5 +
    (1021981665335961675887509605635181201202152317573/3030668377112882756250000000000000000:ℝ)*t^4 +
    (11198760752754982346148437812223082888450889500269551/327333134048770458984375000000000000000:ℝ)*t^3 +
    (12034017163583946742646863911283573660046765892191640401/87288835746338789062500000000000000000000:ℝ)*t^2 +
    (17670011491528419899226529827217130725881483843447001/9713680695874624218750000000000000000000:ℝ)*t^1 +
    (-108348236585674064820049548916655479756645358993/1379457613615331250000000000000000000:ℝ)

theorem frequency_slope_positive (t : ℝ) (ht : 0 < t)
    (hp : frequencyPolynomial t = 0) : 0 < frequencySlope t := by
  have h : t*frequencySlope t-frequencyPolynomial t =
    (5012/6045:ℝ)*t^8 +
    (45363713206799695617936821/737981439382687500000:ℝ)*t^7 +
    (8362584637034098682974692474934473341/28966961788414650000000000000:ℝ)*t^6 +
    (1021981665335961675887509605635181201202152317573/3788335471391103445312500000000000000:ℝ)*t^5 +
    (11198760752754982346148437812223082888450889500269551/436444178731693945312500000000000000000:ℝ)*t^4 +
    (12034017163583946742646863911283573660046765892191640401/130933253619508183593750000000000000000000:ℝ)*t^3 +
    (17670011491528419899226529827217130725881483843447001/19427361391749248437500000000000000000000:ℝ)*t^2 +
    (0/1:ℝ)*t^1 +
    (4750574844864748849091480686980487/60462748788750000000000000000:ℝ) := by
    unfold frequencySlope frequencyPolynomial
    ring
  have hpos : 0 < t*frequencySlope t-frequencyPolynomial t := by
    rw [h]
    positivity
  rw [hp,sub_zero] at hpos
  exact pos_of_mul_pos_right hpos ht.le

/-- At a root, the derivative of the eliminant equals the orientation
determinant of the two frequency equations along the physical reverse family. -/
theorem eliminant_slope_at_root
    (E₀ O₀ E₁ O₁ dE₀ dO₀ dE₁ dO₁ r : ℝ)
    (he : E₀+r*E₁=0) (ho : O₀+r*O₁=0) :
    dO₀*E₁+O₀*dE₁-dE₀*O₁-E₀*dO₁ =
      E₁*(dO₀+r*dO₁)-O₁*(dE₀+r*dE₁) := by
  have he' : E₀ = -r*E₁ := by linarith
  have ho' : O₀ = -r*O₁ := by linarith
  rw [he',ho']
  ring

theorem crossing_quotient_negative (t E₁ O₁ dE dO slope : ℝ)
    (ht : 0 < t) (hs : 0 < slope) (he : slope=E₁*dO-O₁*dE) :
    0 < t*dO^2+dE^2 ∧ -slope/(2*(t*dO^2+dE^2)) < 0 := by
  have hz : dO ≠ 0 ∨ dE ≠ 0 := by
    by_contra h
    push Not at h
    rcases h with ⟨ho,heq⟩
    simp [ho,heq] at he
    linarith
  have hd : 0 < t*dO^2+dE^2 := by
    rcases hz with ho | heq
    · have hh : 0 < dO^2 := sq_pos_of_ne_zero ho
      nlinarith [mul_pos ht hh,sq_nonneg dE]
    · have hh : 0 < dE^2 := sq_pos_of_ne_zero heq
      have hn : 0 ≤ t*dO^2 := mul_nonneg ht.le (sq_nonneg dO)
      linarith
  exact ⟨hd,div_neg_of_neg_of_pos (neg_neg_of_pos hs) (by positivity)⟩

end
end ThreeSitePhosphorylation
