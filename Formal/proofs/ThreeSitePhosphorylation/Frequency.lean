import Mathlib

namespace ThreeSitePhosphorylation
noncomputable section

/-- Elimination and positive reconstruction use real arithmetic, with no division
by an unproved nonzero frequency equation. -/
theorem reverse_reconstruction (t E₀ O₀ E₁ O₁ : ℝ)
    (hphi : O₀*E₁-E₀*O₁ = 0)
    (hd : E₁^2+t*O₁^2 ≠ 0) :
    let r := -(E₀*E₁+t*O₀*O₁)/(E₁^2+t*O₁^2)
    E₀+r*E₁ = 0 ∧ O₀+r*O₁ = 0 := by
  dsimp
  constructor
  · field_simp
    nlinarith [congrArg (fun a : ℝ => a*(t*O₁)) hphi]
  · field_simp
    nlinarith [congrArg (fun a : ℝ => a*E₁) hphi]

def frequencyPolynomial (t : ℝ) : ℝ :=
  (716/6045)*t^8 +
  (45363713206799695617936821/4427888636296125000000)*t^7 +
  (8362584637034098682974692474934473341/144834808942073250000000000000)*t^6 +
  (1021981665335961675887509605635181201202152317573/15153341885564413781250000000000000000)*t^5 +
  (11198760752754982346148437812223082888450889500269551/1309332536195081835937500000000000000000)*t^4 +
  (12034017163583946742646863911283573660046765892191640401/261866507239016367187500000000000000000000)*t^3 +
  (17670011491528419899226529827217130725881483843447001/19427361391749248437500000000000000000000)*t^2 -
  (108348236585674064820049548916655479756645358993/1379457613615331250000000000000000000)*t -
  4750574844864748849091480686980487/60462748788750000000000000000

def frequencyLower : ℝ := 3253896252/100000000000
def frequencyUpper : ℝ := 3253896254/100000000000

theorem frequency_signs : frequencyPolynomial frequencyLower < 0 ∧
    0 < frequencyPolynomial frequencyUpper := by
  norm_num [frequencyPolynomial,frequencyLower,frequencyUpper]

theorem positive_frequency_exists : ∃ t : ℝ,
    frequencyLower ≤ t ∧ t ≤ frequencyUpper ∧ 0 < t ∧ frequencyPolynomial t = 0 := by
  have hab : frequencyLower ≤ frequencyUpper := by norm_num [frequencyLower,frequencyUpper]
  have hc : Continuous frequencyPolynomial := by unfold frequencyPolynomial; fun_prop
  have hm : (0:ℝ) ∈ Set.Icc (frequencyPolynomial frequencyLower)
      (frequencyPolynomial frequencyUpper) := ⟨frequency_signs.1.le,frequency_signs.2.le⟩
  obtain ⟨t,ht,hz⟩ := intermediate_value_Icc hab hc.continuousOn hm
  exact ⟨t,ht.1,ht.2,lt_of_lt_of_le (by norm_num [frequencyLower]) ht.1,hz⟩

end
end ThreeSitePhosphorylation
