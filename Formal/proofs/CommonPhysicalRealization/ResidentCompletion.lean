import proofs.HeritableCompositions.Source

namespace CommonPhysicalRealization.Resident
noncomputable section
open scoped BigOperators

/-- A,B,z,H,F,G,RA,RB,WH, all neutral multiples of one formal element. -/
def element : Fin 9 → ℕ := ![2,1,1,2,1,3,2,1,2]
def left : Fin 6 → Fin 9 → ℕ :=
  ![![1,0,0,0,0,0,0,0,0], ![0,0,1,0,1,0,0,0,0],
    ![0,0,0,1,0,0,0,0,0], ![0,0,0,0,0,0,1,0,0],
    ![0,0,0,0,0,0,0,1,0], ![0,1,0,0,0,1,0,0,0]]
def right : Fin 6 → Fin 9 → ℕ :=
  ![![0,1,1,0,0,0,0,0,0], ![0,0,0,1,0,0,0,0,0],
    ![0,0,2,0,0,0,0,0,0], ![1,0,0,0,0,0,0,0,0],
    ![0,1,0,0,0,0,0,0,0], ![2,0,0,0,0,0,0,0,0]]

theorem balanced (j : Fin 6) :
    (∑ i, left j i * element i) = ∑ i, right j i * element i := by
  revert j
  decide

theorem closed_resident_obstruction (mz mH : ℝ) (hz : 0 < mz)
    (pair1 : mz=mH) (pair2 : mH=2*mz) : False := by linarith

def potential : Fin 9 → ℝ :=
  ![0,0,0,-Real.log 2,3*Real.log 2,0,Real.log 6,Real.log 27,0]
def kp : Fin 6 → ℝ := ![1,16,1,6,27,1/100000]
def km : Fin 6 → ℝ := ![1,1,2,1,1,1/100000]

theorem thermo (j : Fin 6) :
    Real.log (kp j/km j) = ∑ i, ((left j i:ℝ)-right j i)*potential i := by
  have h16 : Real.log 16 = 4*Real.log 2 := by
    simpa only [show (2:ℝ)^4=16 by norm_num, Nat.cast_ofNat] using Real.log_pow (2:ℝ) 4
  have hhalf : Real.log (1/2:ℝ) = -Real.log 2 := by
    rw [one_div,Real.log_inv]
  fin_cases j <;> norm_num [kp,km,left,right,potential,Fin.sum_univ_succ,h16,hhalf]
  ring

/-- The very same density source, with explicit buffered activities on exactly
the directions consuming F,G,RA,RB. Unit activities recover count-level rates. -/
def maintainedPropensity (s : HeritableCompositions.Compartment)
    (aF aG aRA aRB : ℝ) (j : Fin 13) : ℝ :=
  (s.2:ℝ)*FiniteCopy.densityRates (1/100000) (1/(s.2:ℝ))
    (FiniteCopy.concentration s.2 s.1) j *
      (if j=2 then aF else if j=6 then aRA else if j=8 then aRB else if j=10 then aG else 1)

theorem resident_projection (s : HeritableCompositions.Compartment) (j : Fin 13) (γ : ℝ) :
    maintainedPropensity s 1 1 1 1 j = HeritableCompositions.propensity γ s (.inl j) := by
  simp [maintainedPropensity,HeritableCompositions.propensity]

theorem resident_complex_projection (j : Fin 6) (i : Fin 4) :
    ((right j (i.castLE (by decide)):ℤ)-left j (i.castLE (by decide))) =
      FiniteCopy.intJump ⟨2*j.val,by omega⟩ i ∧
    ((left j (i.castLE (by decide)):ℤ)-right j (i.castLE (by decide))) =
      FiniteCopy.intJump ⟨2*j.val+1,by omega⟩ i := by
  revert j i
  decide

/-- Growth consumes one Q and one z and retains them in one size material unit.
Its volume law remains a declared constitutive relation. -/
theorem growth_material (q z : ℝ) (Q nz m : ℕ) (hQ : 1 ≤ Q) (hz : 1 ≤ nz) :
    ((Q-1:ℕ):ℝ)*q+((nz-1:ℕ):ℝ)*z+((m+1:ℕ):ℝ)*(q+z) =
      (Q:ℝ)*q+(nz:ℝ)*z+(m:ℝ)*(q+z) := by
  rw [Nat.cast_sub hQ,Nat.cast_sub hz]
  push_cast
  ring

theorem sink_material : element 3=element 8 := by decide

/-- Coarse source-derived bounds for the maintained resident bill. A and z are
count coordinates and m≥N is the donor's newborn-size lower bound. -/
theorem supply_bounds (N M : ℝ)
    (sz sh sa sb sm : ℝ)
    (hz : sz ≤ 280*N*M) (hh : sh ≤ 280*N*M)
    (ha : sa ≤ 280*N*M) (hb : sb ≤ 280*N*M) (hm : sm ≤ 4*N*M) :
    16*sz+sh ≤ 4760*N*M ∧ 6*sm+sa ≤ 304*N*M ∧ 27*sm+sb ≤ 388*N*M := by
  constructor
  · linarith
  constructor <;> linarith

theorem bimolecular_supply (N m n : ℝ) (hN : 0 < N) (hm : N ≤ m)
    (hn : 0 ≤ n) (hn' : n ≤ 70*N) : n*(n-1)/m ≤ 4900*N := by
  apply (div_le_iff₀ (lt_of_lt_of_le hN hm)).mpr
  have hs : n^2 ≤ (70*N)^2 := sq_le_sq₀ hn (by positivity) |>.mpr hn'
  nlinarith [mul_nonneg (le_of_lt hN) (sub_nonneg.mpr hm)]

end
end CommonPhysicalRealization.Resident
