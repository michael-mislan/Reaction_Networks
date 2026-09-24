import proofs.DynamicSharedResource.SourceCertificate

namespace DynamicSharedResource.Certificate
noncomputable section
open scoped BigOperators

def lower : State := ![8/5,92/25,71/100,71/25000,33/200,3/10,181/2500,729/100]
def upper : State := ![173/100,377/100,711/1000,57/20000,129/500,61/200,729/10000,149/20]

theorem outer_coordinate_bounds (a : State) (ha : InCube 1 a) (i : Fin 8) :
    lower i ≤ reconstruct a i ∧ reconstruct a i ≤ upper i := by
  have h := abs_le.mp (displacement_bound 1 a ha i)
  change lower i ≤ center i+basis.mulVec a i ∧ center i+basis.mulVec a i ≤ upper i
  fin_cases i <;> norm_num [lower,upper,center,width] at * <;> constructor <;> linarith

theorem outer_physical (a : State) (ha : InCube 1 a) : Physical (reconstruct a) := by
  have h0 := outer_coordinate_bounds a ha 0
  have h1 := outer_coordinate_bounds a ha 1
  have h2 := outer_coordinate_bounds a ha 2
  have h3 := outer_coordinate_bounds a ha 3
  have h4 := outer_coordinate_bounds a ha 4
  have h5 := outer_coordinate_bounds a ha 5
  have h6 := outer_coordinate_bounds a ha 6
  have h7 := outer_coordinate_bounds a ha 7
  simp [lower,upper] at h0 h1 h2 h3 h4 h5 h6 h7
  dsimp [Physical,g,e0,y,r]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith⟩

theorem inner_service (a : State) (ha : InCube (1/2) a) :
    10 ≤ HG (reconstruct a) ∧ 4 ≤ HT (reconstruct a) := by
  have ha1 : InCube 1 a := fun i => (ha i).trans (by norm_num)
  have h2 := outer_coordinate_bounds a ha1 2
  have h3 := outer_coordinate_bounds a ha1 3
  have h4 := abs_le.mp (displacement_bound (1/2) a ha 4)
  have h7 := abs_le.mp (displacement_bound (1/2) a ha 7)
  have hz : reconstruct a 4 ≤ 47/200 := by
    change center 4+basis.mulVec a 4 ≤ 47/200
    simp [center,width] at *
    linarith
  have hv : 733/100 ≤ reconstruct a 7 := by
    change 733/100 ≤ center 7+basis.mulVec a 7
    simp [center,width] at *
    linarith
  simp [lower,upper] at h2 h3
  constructor
  · dsimp [HG,e0]
    linarith
  · have hy : 27/100 ≤ y (reconstruct a) := by dsimp [y]; linarith
    have hp := mul_le_mul hy hv (by norm_num : (0:ℝ) ≤ 733/100) (by linarith : 0 ≤ y (reconstruct a))
    dsimp [HT]
    nlinarith

def seed : State := ![0,5/6,0,0,0,0,0,0]
def preparation : State := reconstruct seed
def Prepared (u : State) : Prop := ∀ i, |u i-preparation i| ≤ (1/100000000:ℝ)

theorem preparation_mem : Prepared preparation := by
  intro i
  simp

theorem prepared_contains_ball :
    Metric.ball preparation (1/100000000:ℝ) ⊆ {u | Prepared u} := by
  intro u hu i
  have h := dist_le_pi_dist u preparation i
  rw [Real.dist_eq] at h
  exact h.trans (le_of_lt hu)

theorem preparation_radius_pos : (0:ℝ) < 1/100000000 := by norm_num

set_option maxHeartbeats 2000000 in
theorem preparation_fails : HT preparation < 4 := by
  norm_num [preparation,reconstruct,seed,HT,y,center,basis,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  simp
  norm_num

set_option maxHeartbeats 4000000 in
theorem inverse_preparation_width (i : Fin 8) :
    (∑ j, |inverse i j|)*(1/100000000:ℝ) ≤ 1/12 := by
  fin_cases i <;> norm_num [inverse,Fin.sum_univ_succ]

theorem prepared_in_outer (u : State) (hu : Prepared u) : InCube 1 (coordinates u) := by
  have he : coordinates u = seed+inverse.mulVec (u-preparation) := by
    have hh : u-center = (preparation-center)+(u-preparation) := by abel
    unfold coordinates
    rw [hh,Matrix.mulVec_add]
    have hc := coordinates_reconstruct seed
    change inverse.mulVec (preparation-center)=seed at hc
    rw [hc]
  intro i
  have hd := abs_mulVec_le inverse (u-preparation) (1/100000000) hu i
  have hdi := hd.trans (inverse_preparation_width i)
  have hs : |seed i| ≤ (5/6:ℝ) := by fin_cases i <;> norm_num [seed]
  rw [he,Pi.add_apply]
  exact (abs_add_le _ _).trans (by linarith)

end
end DynamicSharedResource.Certificate
