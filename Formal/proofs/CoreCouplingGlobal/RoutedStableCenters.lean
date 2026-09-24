import proofs.CoreCouplingGlobal.RoutedEnclosures
import proofs.CoreCouplingGlobal.RoutedStableSigns
import proofs.CoreCouplingGlobal.RoutedStableBoxes

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

noncomputable def routedLowRootLower : State := ⟨6483/500,20027/1000,9957/10000,2239/250⟩
noncomputable def routedLowRootUpper : State := ⟨519/40,20029/1000,9959/10000,8959/1000⟩
theorem routedLow_root_enclosure (g z : ℝ)
    (hg : (999999/1000000:ℝ) ≤ g) (hgu : g ≤ 1)
    (hz : z ∈ Icc (9957/10000:ℝ) (9959/10000)) :
    InBox (routedLift g z) routedLowRootLower routedLowRootUpper := by
  have h := routed_lift_enclosure g (9957/10000) (9959/10000) z hg hgu (by norm_num) hz (by norm_num)
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [routedLowerState,routedUpperState] at h1 h2 h3 h4 h5 h6 h7 h8
  norm_num [InBox,routedLowRootLower,routedLowRootUpper]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem routedLow_energy_inBox (x c : State) (hc : InBox c routedLowRootLower routedLowRootUpper)
    (he : energy lowLeft lowRight (transform c) (transform x) ≤ (1/1000000000000:ℝ)) :
    InBox x routedLowLower routedLowUpper := by
  have h := energy_coordinate_small lowLeft lowRight (transform c) (transform x) low_weight_lower he
  have h0 := abs_le.mp (h 0)
  have h1 := abs_le.mp (h 1)
  have h2 := abs_le.mp (h 2)
  have h3 := abs_le.mp (h 3)
  change -(1/200000:ℝ) ≤ (x.A+x.B)-(c.A+c.B) ∧ (x.A+x.B)-(c.A+c.B) ≤ 1/200000 at h0
  change -(1/200000:ℝ) ≤ -x.B-(-c.B) ∧ -x.B-(-c.B) ≤ 1/200000 at h1
  change -(1/200000:ℝ) ≤ x.z-c.z ∧ x.z-c.z ≤ 1/200000 at h2
  change -(1/200000:ℝ) ≤ x.H-c.H ∧ x.H-c.H ≤ 1/200000 at h3
  rcases hc with ⟨k1,k2,k3,k4,k5,k6,k7,k8⟩
  norm_num [routedLowRootLower,routedLowRootUpper] at k1 k2 k3 k4 k5 k6 k7 k8
  norm_num [InBox,routedLowLower,routedLowUpper]
  exact ⟨by linarith [h0.1,h1.1],by linarith [h0.2,h1.2],
    by linarith [h1.2],by linarith [h1.1],by linarith [h2.1],by linarith [h2.2],
    by linarith [h3.1],by linarith [h3.2]⟩


theorem routedLow_center_exists (e g : ℝ)
    (he : (999/100000000:ℝ) ≤ e) (heu : e ≤ 1001/100000000)
    (hg : (999999/1000000:ℝ) ≤ g) (hgu : g ≤ 1) :
    ∃ c : State, c.Positive ∧ RoutedStationary e g c ∧
      InBox c routedLowRootLower routedLowRootUpper := by
  have h1 := routed_stable_sign_lowLeft e g he heu hg hgu
  have h2 := routed_stable_sign_lowRight e g he heu hg hgu
  have hcont : Continuous (routedPoly e g) := by
    unfold routedPoly routedNumerA routedDen routedK
    fun_prop
  obtain ⟨z,hz,hroot⟩ := intermediate_value_Icc (by norm_num : (9957/10000:ℝ) ≤ 9959/10000) hcont.continuousOn
    (show (0:ℝ) ∈ Icc (routedPoly e g (9957/10000)) (routedPoly e g (9959/10000)) by constructor <;> linarith)
  have hgp : 0 < g := by linarith
  have hzp : 0 < z := by linarith [hz.1]
  have hd : routedDen g z ≠ 0 := by
    have hm := mul_pos hgp hzp
    dsimp [routedDen]
    linarith
  exact ⟨routedLift g z,
    routed_lift_positive g z (by linarith) hgu ⟨by linarith [hz.1],by linarith [hz.2]⟩,
    routed_lift_stationary e g z (ne_of_gt hgp) hd hroot,
    routedLow_root_enclosure g z hg hgu hz⟩

noncomputable def routedHighRootLower : State := ⟨5233/250,1507/125,14881/5000,6533/200⟩
noncomputable def routedHighRootUpper : State := ⟨10473/500,6029/500,14883/5000,4084/125⟩
theorem routedHigh_root_enclosure (g z : ℝ)
    (hg : (999999/1000000:ℝ) ≤ g) (hgu : g ≤ 1)
    (hz : z ∈ Icc (14881/5000:ℝ) (14883/5000)) :
    InBox (routedLift g z) routedHighRootLower routedHighRootUpper := by
  have h := routed_lift_enclosure g (14881/5000) (14883/5000) z hg hgu (by norm_num) hz (by norm_num)
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [routedLowerState,routedUpperState] at h1 h2 h3 h4 h5 h6 h7 h8
  norm_num [InBox,routedHighRootLower,routedHighRootUpper]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem routedHigh_energy_inBox (x c : State) (hc : InBox c routedHighRootLower routedHighRootUpper)
    (he : energy highLeft highRight (transform c) (transform x) ≤ (1/1000000000000:ℝ)) :
    InBox x routedHighLower routedHighUpper := by
  have h := energy_coordinate_small highLeft highRight (transform c) (transform x) high_weight_lower he
  have h0 := abs_le.mp (h 0)
  have h1 := abs_le.mp (h 1)
  have h2 := abs_le.mp (h 2)
  have h3 := abs_le.mp (h 3)
  change -(1/200000:ℝ) ≤ (x.A+x.B)-(c.A+c.B) ∧ (x.A+x.B)-(c.A+c.B) ≤ 1/200000 at h0
  change -(1/200000:ℝ) ≤ -x.B-(-c.B) ∧ -x.B-(-c.B) ≤ 1/200000 at h1
  change -(1/200000:ℝ) ≤ x.z-c.z ∧ x.z-c.z ≤ 1/200000 at h2
  change -(1/200000:ℝ) ≤ x.H-c.H ∧ x.H-c.H ≤ 1/200000 at h3
  rcases hc with ⟨k1,k2,k3,k4,k5,k6,k7,k8⟩
  norm_num [routedHighRootLower,routedHighRootUpper] at k1 k2 k3 k4 k5 k6 k7 k8
  norm_num [InBox,routedHighLower,routedHighUpper]
  exact ⟨by linarith [h0.1,h1.1],by linarith [h0.2,h1.2],
    by linarith [h1.2],by linarith [h1.1],by linarith [h2.1],by linarith [h2.2],
    by linarith [h3.1],by linarith [h3.2]⟩


theorem routedHigh_center_exists (e g : ℝ)
    (he : (999/100000000:ℝ) ≤ e) (heu : e ≤ 1001/100000000)
    (hg : (999999/1000000:ℝ) ≤ g) (hgu : g ≤ 1) :
    ∃ c : State, c.Positive ∧ RoutedStationary e g c ∧
      InBox c routedHighRootLower routedHighRootUpper := by
  have h1 := routed_stable_sign_highLeft e g he heu hg hgu
  have h2 := routed_stable_sign_highRight e g he heu hg hgu
  have hcont : Continuous (routedPoly e g) := by
    unfold routedPoly routedNumerA routedDen routedK
    fun_prop
  obtain ⟨z,hz,hroot⟩ := intermediate_value_Icc (by norm_num : (14881/5000:ℝ) ≤ 14883/5000) hcont.continuousOn
    (show (0:ℝ) ∈ Icc (routedPoly e g (14881/5000)) (routedPoly e g (14883/5000)) by constructor <;> linarith)
  have hgp : 0 < g := by linarith
  have hzp : 0 < z := by linarith [hz.1]
  have hd : routedDen g z ≠ 0 := by
    have hm := mul_pos hgp hzp
    dsimp [routedDen]
    linarith
  exact ⟨routedLift g z,
    routed_lift_positive g z (by linarith) hgu ⟨by linarith [hz.1],by linarith [hz.2]⟩,
    routed_lift_stationary e g z (ne_of_gt hgp) hd hroot,
    routedHigh_root_enclosure g z hg hgu hz⟩

end CoreCouplingGlobal
