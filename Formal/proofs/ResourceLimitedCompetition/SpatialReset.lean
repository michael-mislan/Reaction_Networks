import proofs.ResourceLimitedCompetition.SourceSpatial
import proofs.HeritableCompositions.PartitionProduct

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

noncomputable def spatialEnergyValue (N : ℕ) (E : Point → ℝ) (s : Point)
    (c : Compartment) : ℝ :=
  spatialWeight (1/1000000000000000) N c.2*
    Real.exp ((N : ℝ)*localAlpha*E (fun i => concentration c.2 c.1 i-s i))

noncomputable def birthSpatialCeiling (N : ℕ) : ℝ :=
  Real.exp (4*(N : ℝ)*localAlpha*innerEnergy-(N : ℝ)/1000000000000000)

theorem birth_spatial_value (N : ℕ) (E : Point → ℝ) (s : Point) (n : Counts)
    (he : E (fun i => concentration N n i-s i) ≤ 4*innerEnergy) :
    spatialEnergyValue N E s (n,N) ≤ birthSpatialCeiling N := by
  unfold spatialEnergyValue spatialWeight birthSpatialCeiling
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left he
    (by unfold localAlpha; positivity : 0 ≤ (N : ℝ)*localAlpha)
  nlinarith only [h]

theorem birth_spatial_pair_small (N : ℕ)
    (hlarge : (140000000000000000000 : ℝ) ≤ N) : 2*birthSpatialCeiling N ≤ 1 := by
  have hexp : 2*Real.exp (-1 : ℝ) ≤ 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (-1)).le
    have hid : Real.exp (1 : ℝ)*Real.exp (-1 : ℝ)=1 := by
      rw [← Real.exp_add]
      norm_num
    rw [hid] at hh
    linarith only [hh]
  have harg : 4*(N : ℝ)*localAlpha*innerEnergy-(N : ℝ)/1000000000000000 ≤ -1 := by
    unfold localAlpha innerEnergy outerEnergy
    linarith only [hlarge]
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num : (0:ℝ) ≤ 2)).trans hexp

theorem spatial_parent_lower (N : ℕ) (E : Point → ℝ) (s : Point) (n : Counts)
    (hE : ∀ y, 0 ≤ E y) : 1 ≤ spatialEnergyValue N E s (n,2*N) := by
  unfold spatialEnergyValue spatialWeight
  simp only [Nat.cast_mul,Nat.cast_ofNat,sub_self,mul_zero,Real.exp_zero,one_mul]
  apply Real.one_le_exp_iff.mpr
  exact mul_nonneg (by unfold localAlpha; positivity) (hE _)

theorem spatial_pair_reset (N : ℕ)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (E : Point → ℝ) (hE : ∀ y, 0 ≤ E y) (s : Point) (n d : Counts)
    (hgood : E (fun i => concentration N d i-s i) < 4*innerEnergy ∧
      E (fun i => concentration N (fun j => n j-d j) i-s i) < 4*innerEnergy) :
    spatialEnergyValue N E s (d,N)+spatialEnergyValue N E s ((fun i => n i-d i),N) ≤
      spatialEnergyValue N E s (n,2*N) := by
  have h1 := birth_spatial_value N E s d hgood.1.le
  have h2 := birth_spatial_value N E s (fun i => n i-d i) hgood.2.le
  have hsmall := birth_spatial_pair_small N hlarge
  have hparent := spatial_parent_lower N E s n hE
  linarith only [h1,h2,hsmall,hparent]

/-- Actual complementary draw, clipped at failed birth certification. No
independence of siblings or prior cell lifetimes is used. -/
theorem spatial_partition_reset (N : ℕ)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (E : Point → ℝ) (hE : ∀ y, 0 ≤ E y) (s : Point) (n : Counts) :
    (∑ d ∈ daughterDraws n, daughterWeight n d *
      (if E (fun i => concentration N d i-s i) < 4*innerEnergy ∧
          E (fun i => concentration N (fun j => n j-d j) i-s i) < 4*innerEnergy
       then spatialEnergyValue N E s (d,N)+
         spatialEnergyValue N E s ((fun i => n i-d i),N) else 0)) ≤
      spatialEnergyValue N E s (n,2*N) := by
  classical
  have hpoint (d : Counts) :
      (if E (fun i => concentration N d i-s i) < 4*innerEnergy ∧
          E (fun i => concentration N (fun j => n j-d j) i-s i) < 4*innerEnergy
       then spatialEnergyValue N E s (d,N)+
         spatialEnergyValue N E s ((fun i => n i-d i),N) else 0) ≤
      spatialEnergyValue N E s (n,2*N) := by
    split_ifs with h
    · exact spatial_pair_reset N hlarge E hE s n d h
    · exact (by norm_num : (0 : ℝ) ≤ 1).trans (spatial_parent_lower N E s n hE)
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ daughterDraws n) =>
    mul_le_mul_of_nonneg_left (hpoint d) (daughterWeight_nonneg n d))
  simpa only [← Finset.sum_mul,daughterWeight_sum,one_mul] using hsum

end ResourceLimitedCompetition
