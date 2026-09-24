import proofs.ProductiveMemory.ExtractionLocal

namespace ProductiveMemory
open FiniteCopy
noncomputable section
set_option Elab.async false

abbrev ExtractionChannel := Fin 13 ⊕ Unit
def channelJump : ExtractionChannel → Point :=
  Sum.elim jump (fun _ => ![0,0,-1,0])
def channelDensity (rho q : ℝ) (x : Point) : ExtractionChannel → ℝ :=
  Sum.elim (densityRates (1/100000) q x) (fun _ => rho*x 2)
def collectionMark : ExtractionChannel → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

theorem literal_extraction_drift (rho q : ℝ) (x : Point) :
    (fun i => ∑ c : ExtractionChannel, channelDensity rho q x c*channelJump c i) =
    extractDrift rho q x := by
  ext i
  simp only [Fintype.sum_sum_type,channelDensity,channelJump,Sum.elim_inl,Sum.elim_inr]
  simp only [Fintype.sum_unique]
  change drift (1/100000) q x i + rho*x 2*(![0,0,-1,0] : Point) i = _
  unfold extractDrift
  fin_cases i <;> norm_num
  ring

theorem extraction_rate_lattice (rho : ℝ) (N : ℕ) (hN : 0 < N) (n : Counts) :
    (N:ℝ)*channelDensity rho (1/(N:ℝ)) (concentration N n) (.inr ()) = rho*(n 2:ℝ) := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp [channelDensity,concentration]
  field_simp

theorem extraction_rate_nonneg (rho : ℝ) (hr : 0 ≤ rho) (N : ℕ) (n : Counts)
    (c : ExtractionChannel) :
    0 ≤ channelDensity rho (1/(N:ℝ)) (concentration N n) c := by
  cases c with
  | inl c => exact lattice_rates_nonneg (1/100000) (by norm_num) N n c
  | inr c => dsimp [channelDensity,concentration]; positivity

theorem extraction_vanishes_at_zero (rho q : ℝ) (x : Point) (hz : x 2 = 0) :
    channelDensity rho q x (.inr ()) = 0 := by simp [channelDensity,hz]

theorem extraction_z_collection_balance (c : ExtractionChannel) :
    channelJump c 2+(collectionMark c:ℝ) =
      Sum.elim (fun r => jump r 2) (fun _ => 0) c := by
  cases c <;> norm_num [channelJump,collectionMark,Matrix.cons_val_two]

theorem low_extraction_energy_step (y : Point) (q : ℝ) :
    lowExtractionEnergy (fun i => y i+q*(![0,0,-1,0]:Point) i)-lowExtractionEnergy y =
      -2*q*lowExtractionPair y ![0,0,1,0]+(6383792/1000000:ℝ)*q^2 := by
  norm_num [lowExtractionEnergy,lowExtractionPair,Matrix.cons_val_two,Matrix.cons_val_three]
  ring

theorem high_extraction_energy_step (y : Point) (q : ℝ) :
    highExtractionEnergy (fun i => y i+q*(![0,0,-1,0]:Point) i)-highExtractionEnergy y =
      -2*q*highExtractionPair y ![0,0,1,0]+(14137961/1000000:ℝ)*q^2 := by
  norm_num [highExtractionEnergy,highExtractionPair,Matrix.cons_val_two,Matrix.cons_val_three]
  ring

theorem low_extraction_energy_generator (rho m : ℝ) (hm : m ≠ 0) (x center : Point) :
    (rho*m*x 2)*(lowExtractionEnergy (fun i => x i-center i+(1/m)*(![0,0,-1,0]:Point) i)-
      lowExtractionEnergy (fun i => x i-center i)) =
    -2*rho*x 2*lowExtractionPair (fun i => x i-center i) ![0,0,1,0]+
      rho*x 2*(6383792/1000000:ℝ)/m := by
  rw [low_extraction_energy_step]
  field_simp

theorem high_extraction_energy_generator (rho m : ℝ) (hm : m ≠ 0) (x center : Point) :
    (rho*m*x 2)*(highExtractionEnergy (fun i => x i-center i+(1/m)*(![0,0,-1,0]:Point) i)-
      highExtractionEnergy (fun i => x i-center i)) =
    -2*rho*x 2*highExtractionPair (fun i => x i-center i) ![0,0,1,0]+
      rho*x 2*(14137961/1000000:ℝ)/m := by
  rw [high_extraction_energy_step]
  field_simp

end
end ProductiveMemory
