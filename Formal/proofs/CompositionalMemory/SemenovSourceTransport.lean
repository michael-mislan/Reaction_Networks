import proofs.CompositionalMemory.SemenovNoiseBounds

namespace CompositionalMemory.Semenov
open Matrix

noncomputable def channelJump : Channel → Fin 8 → ℝ
  | Sum.inl r,j => stoich r j
  | Sum.inr (Sum.inl i),j => if j=i then 1 else 0
  | Sum.inr (Sum.inr i),j => if j=i then -1 else 0

noncomputable def channelIntensity (n : Fin 8 → ℝ) : Channel → ℝ
  | Sum.inl r => chemicalValue n r
  | Sum.inr (Sum.inl j) => (1/500)*nominalFeed j
  | Sum.inr (Sum.inr j) => (1/500)*n j

theorem channel_intensity_nonneg (n : Fin 8 → ℝ) (hn : ∀ j,0 ≤ n j) (r : Channel) :
    0 ≤ channelIntensity n r := by
  rcases r with r | (j | j)
  · exact chemical_value_nonneg n hn r
  · exact mul_nonneg (by norm_num) (nominalFeed_nonneg j)
  · exact mul_nonneg (by norm_num) (hn j)

/-- Every live finite-source propensity is exactly volume times the nominal
concentration intensity, including all sixteen CSTR flow channels. -/
theorem reactor_rate_scaling (volume : ℝ) (hv : 0 < volume) {B K : ℕ}
    (n : Fin 8 → Fin (B+1)) (c : Fin K) (r : Channel) :
    reactorRate volume (some (n,c)) r=
      volume*channelIntensity (fun j => ((n j).val : ℝ)/volume) r := by
  have hv0 := ne_of_gt hv
  rcases r with r | (j | j)
  · by_cases h7 : r.val=7
    · simp only [reactorRate,channelIntensity,chemicalValue,if_pos h7]
      field_simp
    · simp only [reactorRate,channelIntensity,chemicalValue,if_neg h7]
      field_simp
  · simp only [reactorRate,channelIntensity]
    ring
  · simp only [reactorRate,channelIntensity]
    field_simp

theorem channel_drift_identity (n : Fin 8 → ℝ) (i : Fin 8) :
    (∑ r,channelIntensity n r*channelJump r i)=fieldValue n i := by
  simp only [Fintype.sum_sum_type,channelIntensity,channelJump]
  simp only [mul_ite,mul_one,mul_zero,mul_neg_one]
  simp
  unfold fieldValue
  have he : (∑ r,chemicalValue n r*(stoich r i : ℝ))=(∑ r,(stoich r i : ℝ)*chemicalValue n r) := by
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [he]
  ring

theorem matrix_energy_coordinate (P : Matrix (Fin 8) (Fin 8) ℝ) (j : Fin 8) (c : ℝ) :
    matrixEnergy P (fun i => if i=j then c else 0)=P j j*c^2 := by
  simp [matrixEnergy,mul_ite,ite_mul]
  ring

theorem channel_noise_identity (pc : Fin 8 → Fin 8 → Fin 17 → ℚ) (t : ℝ) (n : Fin 8 → ℝ) :
    (∑ r,channelIntensity n r*matrixEnergy (coefficientMatrix pc t) (channelJump r))=
      metricNoiseValue pc t n := by
  have hc (r : Fin 11) : channelJump (Sum.inl r)=(fun j => (stoich r j : ℝ)) := rfl
  have hf (j : Fin 8) : channelJump (Sum.inr (Sum.inl j))=(fun i => if i=j then (1 : ℝ) else 0) := rfl
  have ho (j : Fin 8) : channelJump (Sum.inr (Sum.inr j))=(fun i => if i=j then (-1 : ℝ) else 0) := rfl
  simp only [Fintype.sum_sum_type,channelIntensity,hc,hf,ho,matrix_energy_coordinate,
    one_pow,neg_one_sq,mul_one]
  unfold metricNoiseValue
  simp only [coefficientMatrix,mul_add,add_mul,Finset.sum_add_distrib]

end CompositionalMemory.Semenov
