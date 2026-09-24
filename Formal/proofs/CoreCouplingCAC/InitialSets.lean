import proofs.CoreCouplingCAC.SelectionEnergy
import proofs.CoreCouplingCAC.EnergyCoordinates

namespace CoreCouplingCAC

def Near (c x : State) : Prop :=
  ∀ i : Fin 4, |transform x i-transform c i| ≤ (1/100000000:ℝ)

theorem near_self (c : State) : Near c c := by
  intro i
  norm_num

theorem near_energy_small (L R : Fin 4 → ℝ) (c x : State)
    (hw : ∀ i, 0 ≤ L i/R i ∧ L i/R i ≤ 100) (hx : Near c x) :
    energy L R (transform c) (transform x) ≤ (1/1000000000000:ℝ) := by
  have he : ∀ i : Fin 4, (L i/R i)*(transform x i-transform c i)^2 ≤
      100*(1/100000000:ℝ)^2 := by
    intro i
    have ha := abs_le.mp (hx i)
    have hs : (transform x i-transform c i)^2 ≤ (1/100000000:ℝ)^2 := by
      nlinarith [ha.1,ha.2]
    exact (mul_le_mul_of_nonneg_right (hw i).2 (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hs (by norm_num))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => he i)
  norm_num at hs
  exact hs.trans (by norm_num)

theorem low_near_energy (c x : State) (hx : Near c x) :
    energy lowLeft lowRight (transform c) (transform x) ≤ (1/1000000000000:ℝ) := by
  exact near_energy_small lowLeft lowRight c x
    (by intro i; fin_cases i <;> norm_num [lowLeft,lowRight]) hx

theorem high_near_energy (c x : State) (hx : Near c x) :
    energy highLeft highRight (transform c) (transform x) ≤ (1/1000000000000:ℝ) := by
  exact near_energy_small highLeft highRight c x
    (by intro i; fin_cases i <;> norm_num [highLeft,highRight]) hx

theorem low_weight_lower (i : Fin 4) : (1/4:ℝ) ≤ lowLeft i/lowRight i := by
  fin_cases i <;> norm_num [lowLeft,lowRight]
theorem high_weight_lower (i : Fin 4) : (1/4:ℝ) ≤ highLeft i/highRight i := by
  fin_cases i <;> norm_num [highLeft,highRight]

theorem low_energy_inBox (x c : State) (hc : InBox c lowRootLower lowRootUpper)
    (he : energy lowLeft lowRight (transform c) (transform x) ≤ (1/1000000000000:ℝ)) :
    InBox x lowLower lowUpper := by
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
  norm_num [lowRootLower,lowRootUpper] at k1 k2 k3 k4 k5 k6 k7 k8
  norm_num [InBox,lowLower,lowUpper]
  exact ⟨by linarith [h0.1,h1.1],by linarith [h0.2,h1.2],
    by linarith [h1.2],by linarith [h1.1],by linarith [h2.1],by linarith [h2.2],
    by linarith [h3.1],by linarith [h3.2]⟩

theorem high_energy_inBox (x c : State) (hc : InBox c highRootLower highRootUpper)
    (he : energy highLeft highRight (transform c) (transform x) ≤ (1/1000000000000:ℝ)) :
    InBox x highLower highUpper := by
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
  norm_num [highRootLower,highRootUpper] at k1 k2 k3 k4 k5 k6 k7 k8
  norm_num [InBox,highLower,highUpper]
  exact ⟨by linarith [h0.1,h1.1],by linarith [h0.2,h1.2],
    by linarith [h1.2],by linarith [h1.1],by linarith [h2.1],by linarith [h2.2],
    by linarith [h3.1],by linarith [h3.2]⟩

theorem low_box_norm (x : State) (hx : InBox x lowLower lowUpper) : ‖transform x‖ ≤ 100 := by
  rcases hx with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [lowLower,lowUpper] at h1 h2 h3 h4 h5 h6 h7 h8
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 100)).2
  intro i
  fin_cases i <;> simp [transform,Real.norm_eq_abs,abs_le] <;> constructor <;> linarith

theorem high_box_norm (x : State) (hx : InBox x highLower highUpper) : ‖transform x‖ ≤ 100 := by
  rcases hx with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [highLower,highUpper] at h1 h2 h3 h4 h5 h6 h7 h8
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 100)).2
  intro i
  fin_cases i <;> simp [transform,Real.norm_eq_abs,abs_le] <;> constructor <;> linarith

theorem low_box_positive (x : State) (hx : InBox x lowLower lowUpper) : x.Positive := by
  rcases hx with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [lowLower,lowUpper] at h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem high_box_positive (x : State) (hx : InBox x highLower highUpper) : x.Positive := by
  rcases hx with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [highLower,highUpper] at h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

end CoreCouplingCAC
