import Mathlib

namespace DynamicSharedResource
noncomputable section

abbrev State := Fin 8 → ℝ
def g (u : State) : ℝ := 9289/25 - 2*u 1-u 3
def e0 (u : State) : ℝ := 50-u 2-u 3
def y (u : State) : ℝ := 101/200-u 4
def r (u : State) : ℝ := 2387/125-u 5-u 6-u 7
def HG (u : State) : ℝ := (21/100)*e0 u
def HT (u : State) : ℝ := (21/10)*y u*u 7
def phi1 (u : State) : ℝ := (1/25)*g u*u 2
def phi2 (u : State) : ℝ := 10*g u*u 3
def psiG (u : State) : ℝ := (16/5)*u 0*(u 1-89/50)
def psiT (u : State) : ℝ := 20*u 0*(u 4-3/40)
def regen (s x : ℝ) : ℝ := s*375*(30-x)/(873/10-x)
def thetaR (u : State) : ℝ := (2/5)*r u
def thetaW (sigma : ℝ) (u : State) : ℝ := sigma*(9/12500)*u 5
def thetaH (sigma : ℝ) (u : State) : ℝ := sigma*(3/1000)*u 6
def thetaV (u : State) : ℝ := 15*u 5

def field (s sigma : ℝ) (u : State) : State :=
  ![regen s (u 0)-psiG u-psiT u, phi2 u-psiG u,
    HG u-phi1 u, phi1 u-phi2 u, HT u-psiT u,
    thetaR u+thetaH sigma u-thetaW sigma u-thetaV u,
    thetaW sigma u-thetaH sigma u, thetaV u-HT u]

def nominal : State → State := field (3/25) 1
def Physical (u : State) : Prop :=
  0 ≤ u 0 ∧ u 0 ≤ 30 ∧ 89/50 ≤ u 1 ∧ 3/40 ≤ u 4 ∧
  0 ≤ g u ∧ 0 ≤ e0 u ∧ 0 ≤ u 2 ∧ 0 ≤ u 3 ∧ 0 ≤ y u ∧
  0 ≤ r u ∧ 0 ≤ u 5 ∧ 0 ≤ u 6 ∧ 0 ≤ u 7

def BG (u : State) : ℝ := (u 1-89/50)+u 2+u 3
def BT (u : State) : ℝ := u 4-3/40
def W (u : State) : ℝ := 23443/100+u 0-BG u-BT u

theorem bufferG_velocity (s sigma : ℝ) (u : State) :
    field s sigma u 1+field s sigma u 2+field s sigma u 3 = HG u-psiG u := by
  simp [field]
  ring

theorem bufferT_velocity (s sigma : ℝ) (u : State) :
    field s sigma u 4 = HT u-psiT u := by simp [field]

theorem resource_velocity (s sigma : ℝ) (u : State) :
    field s sigma u 0-(field s sigma u 1+field s sigma u 2+field s sigma u 3)-
      field s sigma u 4 = regen s (u 0)-HG u-HT u := by
  simp [field]
  ring

theorem peroxide_velocity (s sigma : ℝ) (u : State) :
    HG u+thetaR u+thetaW sigma u = HG u+HT u+thetaH sigma u+
      field s sigma u 6+(field s sigma u 5+field s sigma u 6+field s sigma u 7) := by
  simp [field]
  ring

theorem denominator_separated (u : State) (hu : Physical u) :
    573/10 ≤ 873/10-u 0 := by linarith [hu.2.1]

theorem bufferG_hasDerivAt (s sigma : ℝ) (u : ℝ → State) (t : ℝ)
    (hu : HasDerivAt u (field s sigma (u t)) t) :
    HasDerivAt (fun t => BG (u t)) (HG (u t)-psiG (u t)) t := by
  have hd := hasDerivAt_pi.1 hu
  simpa only [BG,bufferG_velocity] using
    (((hd 1).sub_const (89/50)).add (hd 2)).add (hd 3)

theorem bufferT_hasDerivAt (s sigma : ℝ) (u : ℝ → State) (t : ℝ)
    (hu : HasDerivAt u (field s sigma (u t)) t) :
    HasDerivAt (fun t => BT (u t)) (HT (u t)-psiT (u t)) t := by
  simpa only [BT,bufferT_velocity] using (hasDerivAt_pi.1 hu 4).sub_const (3/40)

theorem resource_hasDerivAt (s sigma : ℝ) (u : ℝ → State) (t : ℝ)
    (hu : HasDerivAt u (field s sigma (u t)) t) :
    HasDerivAt (fun t => W (u t)) (regen s (u t 0)-HG (u t)-HT (u t)) t := by
  convert (((hasDerivAt_pi.1 hu 0).const_add (23443/100)).sub
    (bufferG_hasDerivAt s sigma u t hu)).sub (bufferT_hasDerivAt s sigma u t hu) using 1
  simp [field]
  ring

end
end DynamicSharedResource
