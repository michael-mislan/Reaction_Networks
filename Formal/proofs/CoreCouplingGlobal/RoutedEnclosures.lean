import proofs.CoreCouplingGlobal.RoutedResponse
import proofs.CoreCouplingCAC.LocalBounds

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

noncomputable def routedLowerState (l r : ℝ) : State :=
  ⟨l*(60/(3-999999/1000000+r))+
    ((20004*l^2-159984*r)/20001)/(999999/1000000),
    60/(3-999999/1000000+r),l,(160000*l+20000*l^2)/20001⟩
noncomputable def routedUpperState (l r : ℝ) : State :=
  ⟨r*(60/(2+(999999/1000000)*l))+(20004*r^2-159984*l)/20001,
    60/(2+(999999/1000000)*l),r,(160000*r+20000*r^2)/20001⟩

theorem routed_lift_enclosure (g l r z : ℝ)
    (hg : (999999/1000000:ℝ) ≤ g) (hgu : g ≤ 1) (hl : 0 < l)
    (hz : z ∈ Icc l r) (hk : 20004*r^2-159984*l ≤ 0) :
    InBox (routedLift g z) (routedLowerState l r) (routedUpperState l r) := by
  have hgp : 0 < g := by linarith
  have hzp : 0 < z := hl.trans_le hz.1
  have hr : 0 < r := hzp.trans_le hz.2
  have hgz := mul_le_mul hg hz.1 hl.le hgp.le
  have hgzu := mul_le_mul hgu hz.2 hzp.le (by norm_num : (0:ℝ) ≤ 1)
  have hdlo : 2+(999999/1000000)*l ≤ routedDen g z := by
    dsimp [routedDen]; nlinarith
  have hdhi : routedDen g z ≤ 3-999999/1000000+r := by
    dsimp [routedDen]; nlinarith
  have hd : 0 < routedDen g z := (by positivity : 0 < 2+(999999/1000000)*l).trans_le hdlo
  have hB₁ : 60/(3-999999/1000000+r) ≤ 60/routedDen g z := by
    apply (div_le_div_iff₀ (by linarith) hd).2
    linarith
  have hB₂ : 60/routedDen g z ≤ 60/(2+(999999/1000000)*l) := by
    apply (div_le_div_iff₀ hd (by positivity)).2
    linarith
  have hsq₁ : l^2 ≤ z^2 := by nlinarith [sq_nonneg (z-l),hz.1]
  have hsq₂ : z^2 ≤ r^2 := by nlinarith [sq_nonneg (r-z),hz.2]
  let klo : ℝ := (20004*l^2-159984*r)/20001
  let khi : ℝ := (20004*r^2-159984*l)/20001
  have hkl : klo ≤ routedK z := by dsimp [klo,routedK]; nlinarith [hz.2]
  have hku : routedK z ≤ khi := by dsimp [khi,routedK]; nlinarith [hz.1]
  have hkhi : khi ≤ 0 := by dsimp [khi]; linarith
  have hklo : klo ≤ 0 := le_trans hkl (le_trans hku hkhi)
  have hkglo : klo/(999999/1000000) ≤ routedK z/g := by
    apply (div_le_div_iff₀ (by norm_num) hgp).2
    have hm := mul_le_mul_of_nonpos_left hg hklo
    nlinarith
  have hkghi : routedK z/g ≤ khi := by
    apply (div_le_iff₀ hgp).2
    have hm := mul_le_mul_of_nonpos_left hgu hkhi
    nlinarith
  have hA₁ := mul_le_mul hz.1 hB₁ (by positivity : (0:ℝ) ≤ 60/(3-999999/1000000+r)) hzp.le
  have hA₂ := mul_le_mul hz.2 hB₂ (by positivity : (0:ℝ) ≤ 60/routedDen g z) hr.le
  have hid : (routedLift g z).A = z*(60/routedDen g z)+routedK z/g := by
    dsimp [routedLift,routedNumerA]
    field_simp
  have hH : (routedLift g z).H = (160000*z+20000*z^2)/20001 := by
    dsimp [routedLift]
    ring
  unfold InBox
  refine ⟨?_,?_,hB₁,hB₂,hz.1,hz.2,?_,?_⟩
  · rw [hid]
    dsimp [routedLowerState]
    change l*(60/(3-999999/1000000+r))+klo/(999999/1000000) ≤ _
    linarith
  · rw [hid]
    dsimp [routedUpperState]
    change _ ≤ r*(60/(2+(999999/1000000)*l))+khi
    linarith
  · rw [hH]
    dsimp [routedLowerState]
    nlinarith [hz.1]
  · rw [hH]
    dsimp [routedUpperState]
    nlinarith [hz.2]
end CoreCouplingGlobal
