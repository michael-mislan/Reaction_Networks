import proofs.CompositionalMemory.GenericGlobalReactions

namespace CompositionalMemory

theorem general_membrane_rate_bounds {k d : ℕ} (hk : 1 ≤ k)
    (z : Fin d) (s : GeneralCountState k d) (hm : 0 < s.2)
    (γ lo hi : ℝ) (hγ : 0 ≤ γ)
    (hz : ∀ i, lo ≤ generalConcentration s i z ∧ generalConcentration s i z ≤ hi) :
    γ*(s.2:ℝ)*lo ≤ ∑ i, γ*(s.1 i z:ℝ) ∧
      (∑ i, γ*(s.1 i z:ℝ)) ≤ γ*(s.2:ℝ)*hi := by
  let v := (s.2:ℝ)/k
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hm0 : (s.2:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hcount (i) : v*generalConcentration s i z=(s.1 i z:ℝ) := by
    dsimp [v,generalConcentration]
    field_simp
  have hvol : v*(k:ℝ)=(s.2:ℝ) := by dsimp [v]; field_simp
  have hsum : (∑ i, γ*(s.1 i z:ℝ))=γ*v*(∑ i, generalConcentration s i z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc,hcount]
  have hconst (X : ℝ) : γ*v*((k:ℝ)*X)=γ*(s.2:ℝ)*X := by
    calc
      _ = γ*(v*k)*X := by ring
      _ = _ := by rw [hvol]
  have hlo : (k:ℝ)*lo ≤ ∑ i, generalConcentration s i z := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hz i).1)
  have hhi : (∑ i, generalConcentration s i z) ≤ (k:ℝ)*hi := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hz i).2)
  rw [hsum]
  exact ⟨by simpa only [hconst] using mul_le_mul_of_nonneg_left hlo (mul_nonneg hγ hv),
    by simpa only [hconst] using mul_le_mul_of_nonneg_left hhi (mul_nonneg hγ hv)⟩

theorem general_membrane_bounded_activity {k d : ℕ} (hk : 1 ≤ k)
    (z : Fin d) (s : GeneralCountState k d) (M : ℕ) (hM : 0 < M)
    (hm : M ≤ s.2 ∧ s.2 ≤ 2*M) (γ lo hi : ℝ)
    (hγ : 0 ≤ γ) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hz : ∀ i, lo ≤ generalConcentration s i z ∧ generalConcentration s i z ≤ hi) :
    (γ*lo)*(M:ℝ) ≤ ∑ i, γ*(s.1 i z:ℝ) ∧
      (∑ i, γ*(s.1 i z:ℝ)) ≤ 2*(γ*hi)*(M:ℝ) := by
  have hh := general_membrane_rate_bounds hk z s (hM.trans_le hm.1) γ lo hi hγ hz
  have hml : (M:ℝ) ≤ s.2 := by exact_mod_cast hm.1
  have hmu : (s.2:ℝ) ≤ 2*(M:ℝ) := by exact_mod_cast hm.2
  constructor
  · have h := mul_le_mul_of_nonneg_left hml (mul_nonneg hγ hlo)
    nlinarith only [h,hh.1]
  · have h := mul_le_mul_of_nonneg_left hmu (mul_nonneg hγ hhi)
    nlinarith only [h,hh.2]

end CompositionalMemory
