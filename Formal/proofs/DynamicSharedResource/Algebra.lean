import proofs.DynamicSharedResource.Model

namespace DynamicSharedResource
noncomputable section
open scoped BigOperators

def jac (c : State) : Matrix (Fin 8) (Fin 8) ℝ := ![
  ![-45*(573/10)/(873/10-c 0)^2-(16/5)*(c 1-89/50)-20*(c 4-3/40),
    -(16/5)*c 0,0,0,-20*c 0,0,0,0],
  ![-(16/5)*(c 1-89/50),-20*c 3-(16/5)*c 0,0,10*g c-10*c 3,0,0,0,0],
  ![0,(2/25)*c 2,-21/100-(1/25)*g c,-21/100+(1/25)*c 2,0,0,0,0],
  ![0,-(2/25)*c 2+20*c 3,(1/25)*g c,-(1/25)*c 2-10*g c+10*c 3,0,0,0,0],
  ![-20*(c 4-3/40),0,0,0,-(21/10)*c 7-20*c 0,0,0,(21/10)*y c],
  ![0,0,0,0,0,-2/5-9/12500-15,3/1000-2/5,-2/5],
  ![0,0,0,0,0,9/12500,-3/1000,0],
  ![0,0,0,0,(21/10)*c 7,15,0,-(21/10)*y c]]

def reaction : Matrix (Fin 8) (Fin 5) ℝ := ![
  ![-16/5,-20,0,0,0], ![-16/5,0,0,10,0],
  ![0,0,-1/25,0,0], ![0,0,1/25,-10,0],
  ![0,-20,0,0,-21/10], ![0,0,0,0,0], ![0,0,0,0,0], ![0,0,0,0,21/10]]

def products (d : State) : Fin 5 → ℝ :=
  ![d 0*d 1,d 0*d 4,(-2*d 1-d 3)*d 2,(-2*d 1-d 3)*d 3,d 4*d 7]

def sourceRemainder (c d : State) : ℝ :=
  -45*(573/10)*(d 0)^2/((873/10-c 0)^2*(873/10-c 0-d 0))

def sourceVector (a : ℝ) : State := ![a,0,0,0,0,0,0,0]

theorem fraction_expansion (a b z : ℝ) (ha : a ≠ 0) (haz : a-z ≠ 0) :
    (b-z)/(a-z) = b/a + ((b-a)/a^2)*z + ((b-a)*z^2)/(a^2*(a-z)) := by
  field_simp
  ring

theorem regen_expansion (x dx : ℝ) (hx : 873/10-x ≠ 0)
    (hxd : 873/10-x-dx ≠ 0) :
    regen (3/25) (x+dx) = regen (3/25) x -
      45*(573/10)/(873/10-x)^2*dx -
      45*(573/10)*dx^2/((873/10-x)^2*(873/10-x-dx)) := by
  have h := fraction_expansion (873/10-x) (30-x) dx hx hxd
  have he : (30-x)-(873/10-x) = -(573/10:ℝ) := by ring
  rw [he] at h
  unfold regen
  have hxsum : 873/10-(x+dx) = 873/10-x-dx := by ring
  have hb : 30-(x+dx) = 30-x-dx := by ring
  rw [hxsum,hb]
  norm_num
  linear_combination 45*h

set_option maxHeartbeats 600000 in
theorem nominal_expansion (c d : State)
    (hc : 873/10-c 0 ≠ 0) (hcd : 873/10-c 0-d 0 ≠ 0) :
    nominal (c+d) = nominal c + (jac c).mulVec d + reaction.mulVec (products d) +
      sourceVector (sourceRemainder c d) := by
  funext i
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  fin_cases i <;>
    simp [nominal,field,jac,reaction,products,sourceVector,sourceRemainder,
      HG,HT,phi1,phi2,psiG,psiT,
      thetaR,thetaW,thetaH,thetaV,g,e0,y,r]
  · rw [regen_expansion (c 0) (d 0) hc hcd]
    ring
  all_goals ring

end
end DynamicSharedResource
