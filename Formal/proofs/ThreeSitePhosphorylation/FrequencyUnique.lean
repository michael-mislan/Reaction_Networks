import proofs.ThreeSitePhosphorylation.FrequencyData

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 1000000

def scaledFrequency (t : ℝ) : ℝ :=
    (716/6045:ℝ)*t^7 +
    (45363713206799695617936821/4427888636296125000000:ℝ)*t^6 +
    (8362584637034098682974692474934473341/144834808942073250000000000000:ℝ)*t^5 +
    (1021981665335961675887509605635181201202152317573/15153341885564413781250000000000000000:ℝ)*t^4 +
    (11198760752754982346148437812223082888450889500269551/1309332536195081835937500000000000000000:ℝ)*t^3 +
    (12034017163583946742646863911283573660046765892191640401/261866507239016367187500000000000000000000:ℝ)*t^2 +
    (17670011491528419899226529827217130725881483843447001/19427361391749248437500000000000000000000:ℝ)*t^1 +
    (-108348236585674064820049548916655479756645358993/1379457613615331250000000000000000000:ℝ) + (-4750574844864748849091480686980487/60462748788750000000000000000:ℝ)/t

theorem scaled_frequency_identity (t : ℝ) (ht : t ≠ 0) :
    scaledFrequency t = frequencyPolynomial t / t := by
  unfold scaledFrequency frequencyPolynomial
  field_simp
  ring

theorem scaled_frequency_strictMono : StrictMonoOn scaledFrequency (Set.Ioi 0) := by
  intro a ha b hb hab
  change 0 < a at ha
  change 0 < b at hb
  unfold scaledFrequency
  simp only [neg_div]
  gcongr

theorem positive_frequency_unique (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hpa : frequencyPolynomial a = 0) (hpb : frequencyPolynomial b = 0) : a=b := by
  apply scaled_frequency_strictMono.injOn ha hb
  rw [scaled_frequency_identity a (ne_of_gt ha),scaled_frequency_identity b (ne_of_gt hb),hpa,hpb]
  simp

end
end ThreeSitePhosphorylation
