import proofs.HeritableCompositions.Main
import proofs.FiniteCopy.ActivityH

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

noncomputable def activityDisplacement : Point := ![0,0,-3/20000,1/10000]

theorem activity_displacement_inside : lowEnergy activityDisplacement < 4*innerEnergy ∧
    highEnergy activityDisplacement < 4*innerEnergy := by
  norm_num [lowEnergy,highEnergy,activityDisplacement,innerEnergy,outerEnergy,Matrix.cons_val_two,Matrix.cons_val_three]

theorem shifted_H_current_negative (z H : ℝ) (hz : 0 ≤ z) (hz3 : z ≤ 3)
    (hs : 16*z+2*z^2-(2+1/10000)*H=0) :
    16*(z-3/20000)-2*(H+1/10000)+2*(z-3/20000)^2 < 0 := by
  have hzsq : z^2 ≤ 3*z := by nlinarith only [mul_nonneg hz (sub_nonneg.mpr hz3)]
  have hH : H ≤ 12*z := by nlinarith only [hs,hzsq,hz]
  nlinarith only [hs,hH,hz3]

theorem all_or_nothing_partition_obstruction (P : Counts → Prop) (hzero : ¬ P (fun _ => 0))
    (n : Counts) : ¬(P n ∧ P (fun _ => 0)) ∧ ¬(P (fun _ => 0) ∧ P n) := by
  exact ⟨fun h => hzero h.2,fun h => hzero h.1⟩

theorem low_birth_not_empty (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) (hγ : 0 ≤ γ) (hmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N) (n : BirthCount (lowCertificate z γ hz hs hγ hmax) N) :
    n.val ≠ (fun _ => 0) := by
  intro hn
  have h := low_birth_readout z γ hz hs hγ hmax N hN n
  simp [compositionalReadout,hn] at h

theorem high_birth_not_empty (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) (hγ : 0 ≤ γ) (hmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N) (n : BirthCount (highCertificate z γ hz hs hγ hmax) N) :
    n.val ≠ (fun _ => 0) := by
  intro hn
  have h := high_birth_readout z γ hz hs hγ hmax N hN n
  simp [compositionalReadout,hn] at h

end HeritableCompositions
