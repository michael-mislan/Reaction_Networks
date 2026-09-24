import proofs.ProductiveMemory.ExtractionScaling
import proofs.ProductiveMemory.ExtractionGrowthPair

namespace ProductiveMemory
open FiniteCopy HeritableCompositions Set
noncomputable section
set_option Elab.async false

def extractGrowthGenerator (rho γ : ℝ) (m : ℕ) (f : Point → ℝ) (x : Point) : ℝ :=
  countGenerator rho m f x + γ*(m:ℝ)*x 2*
    (f (fun i => x i-(1/((m:ℝ)+1))*(x i+membraneDirection i))-f x)

theorem low_extraction_resident_birth (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (he : extractDrift rho 0 (lift rho z) = 0)
    (N m : ℕ) (hm : 1 ≤ m) (hNm : N ≤ m) (n : Counts)
    (hy : ∀ i, |concentration m n i-lift rho z i| ≤ 1/400)
    (hs : ∀ i, lift rho z i ≤ 34) :
    countGenerator rho m ((energyExponential lowExtractionEnergy) N (lift rho z)) (concentration m n) ≤
      localAlpha*(energyExponential lowExtractionEnergy) N (lift rho z) (concentration m n)*
        (-(N:ℝ)/2*normSq (fun i => concentration m n i-lift rho z i)+100000000) := by
  let s := lift rho z
  let E := fun x : Point => lowExtractionEnergy (fun i => x i-s i)
  have hsource := low_count_generator rho z hr hz he m hm n hy hs
  unfold energyExponential at hsource ⊢
  have h := extraction_scaled_dissipation rho localAlpha
    (normSq (fun i => concentration m n i-s i)) 100000000 (by linarith [hr.1])
    (by norm_num [localAlpha]) (by norm_num) N m hm hNm n E
    (by simpa only [E,s,mul_assoc,mul_left_comm,mul_comm] using hsource)
  simpa only [E,s,mul_assoc,mul_left_comm,mul_comm] using h

theorem low_extraction_membrane_bound (γ : ℝ) (N m : ℕ) (s x : Point)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000) (hm : 1 ≤ m) (hNm : N ≤ m)
    (hx : ∀ i, |x i| ≤ 35) (hz : 0 ≤ x 2 ∧ x 2 ≤ 4)
    (hy : normSq (fun i => x i-s i) ≤ 1/160000) :
    γ*(m : ℝ)*x 2*((energyExponential lowExtractionEnergy) N s
      (fun i => x i-(1/((m : ℝ)+1))*(x i+membraneDirection i))-(energyExponential lowExtractionEnergy) N s x) ≤
    localAlpha*(energyExponential lowExtractionEnergy) N s x*
      ((N : ℝ)*normSq (fun i => x i-s i)/4+8000000000*(N : ℝ)*γ^2+1) := by
  let y : Point := fun i => x i-s i
  let v : Point := fun i => x i+membraneDirection i
  let q : ℝ := 1/((m : ℝ)+1)
  let r := Real.sqrt (normSq y)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hsq : r^2=normSq y := Real.sq_sqrt (normSq_nonneg y)
  have hrmax : r ≤ 1/400 := by nlinarith only [hsq,hr,hy]
  have hv := membrane_vector_bounds x hx
  have hp := low_extraction_pair_box y v r hr (coordinate_le_radius y) hv.1
  have hL : |-2*lowExtractionPair y v| ≤ 14400*r := by
    rw [abs_mul]
    norm_num
    linarith only [hp,hr]
  have hQ : 0 ≤ lowExtractionEnergy v := by
    linarith only [lowExtractionEnergy_lower v,normSq_nonneg v]
  have hQmax : lowExtractionEnergy v ≤ 211722 := by
    exact low_extraction_membrane_energy v hv.1
  have hE : lowExtractionEnergy (fun i => (x i-q*v i)-s i) =
      lowExtractionEnergy y+q*(-2*lowExtractionPair y v)+q^2*lowExtractionEnergy v := by
    have hid : (fun i => (x i-q*v i)-s i)=(fun i => y i-q*v i) := by
      funext i
      dsimp [y]
      ring
    rw [hid,low_extraction_energy_sub]
    ring
  have h := membrane_observable_bound γ (N : ℝ) (m : ℝ) (x 2) r
    (lowExtractionEnergy y) (lowExtractionEnergy (fun i => (x i-q*v i)-s i))
    (-2*lowExtractionPair y v) (lowExtractionEnergy v) hγ hγmax (Nat.cast_nonneg N)
    (by exact_mod_cast hm) (by exact_mod_cast hNm) hz.1 hz.2 hrmax hL hQ hQmax hE
  rw [hsq] at h
  simpa only [energyExponential,y,v,q] using h


theorem low_extraction_growing_bound (rho z γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (he : extractDrift rho 0 (lift rho z) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N m : ℕ) (hm : 1 ≤ m) (hNm : N ≤ m) (n : Counts)
    (hy : ∀ i, |concentration m n i-lift rho z i| ≤ 1/400)
    (hnorm : normSq (fun i => concentration m n i-lift rho z i) ≤ 1/160000)
    (hx : ∀ i, |concentration m n i| ≤ 35)
    (hxz : 0 ≤ concentration m n 2 ∧ concentration m n 2 ≤ 4)
    (hs : ∀ i, lift rho z i ≤ 34) :
    extractGrowthGenerator rho γ m ((energyExponential lowExtractionEnergy) N (lift rho z)) (concentration m n) ≤
      localAlpha*(energyExponential lowExtractionEnergy) N (lift rho z) (concentration m n)*
        (-(N:ℝ)/4*normSq (fun i => concentration m n i-lift rho z i)+
          200000000+8000000000*(N:ℝ)*γ^2) := by
  have hres := low_extraction_resident_birth rho z hr hz he N m hm hNm n hy hs
  have hmem := low_extraction_membrane_bound γ N m (lift rho z)
    (concentration m n) hγ hγmax hm hNm hx hxz hnorm
  have hpos : 0 ≤ localAlpha*(energyExponential lowExtractionEnergy) N (lift rho z) (concentration m n) := by
    unfold localAlpha energyExponential
    positivity
  unfold extractGrowthGenerator
  nlinarith only [hres,hmem,hpos]

theorem high_extraction_resident_birth (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (he : extractDrift rho 0 (lift rho z) = 0)
    (N m : ℕ) (hm : 1 ≤ m) (hNm : N ≤ m) (n : Counts)
    (hy : ∀ i, |concentration m n i-lift rho z i| ≤ 1/400)
    (hs : ∀ i, lift rho z i ≤ 34) :
    countGenerator rho m ((energyExponential highExtractionEnergy) N (lift rho z)) (concentration m n) ≤
      localAlpha*(energyExponential highExtractionEnergy) N (lift rho z) (concentration m n)*
        (-(N:ℝ)/2*normSq (fun i => concentration m n i-lift rho z i)+100000000) := by
  let s := lift rho z
  let E := fun x : Point => highExtractionEnergy (fun i => x i-s i)
  have hsource := high_count_generator rho z hr hz he m hm n hy hs
  unfold energyExponential at hsource ⊢
  have h := extraction_scaled_dissipation rho localAlpha
    (normSq (fun i => concentration m n i-s i)) 100000000 (by linarith [hr.1])
    (by norm_num [localAlpha]) (by norm_num) N m hm hNm n E
    (by simpa only [E,s,mul_assoc,mul_left_comm,mul_comm] using hsource)
  simpa only [E,s,mul_assoc,mul_left_comm,mul_comm] using h

theorem high_extraction_membrane_bound (γ : ℝ) (N m : ℕ) (s x : Point)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000) (hm : 1 ≤ m) (hNm : N ≤ m)
    (hx : ∀ i, |x i| ≤ 35) (hz : 0 ≤ x 2 ∧ x 2 ≤ 4)
    (hy : normSq (fun i => x i-s i) ≤ 1/160000) :
    γ*(m : ℝ)*x 2*((energyExponential highExtractionEnergy) N s
      (fun i => x i-(1/((m : ℝ)+1))*(x i+membraneDirection i))-(energyExponential highExtractionEnergy) N s x) ≤
    localAlpha*(energyExponential highExtractionEnergy) N s x*
      ((N : ℝ)*normSq (fun i => x i-s i)/4+8000000000*(N : ℝ)*γ^2+1) := by
  let y : Point := fun i => x i-s i
  let v : Point := fun i => x i+membraneDirection i
  let q : ℝ := 1/((m : ℝ)+1)
  let r := Real.sqrt (normSq y)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hsq : r^2=normSq y := Real.sq_sqrt (normSq_nonneg y)
  have hrmax : r ≤ 1/400 := by nlinarith only [hsq,hr,hy]
  have hv := membrane_vector_bounds x hx
  have hp := high_extraction_pair_box y v r hr (coordinate_le_radius y) hv.1
  have hL : |-2*highExtractionPair y v| ≤ 14400*r := by
    rw [abs_mul]
    norm_num
    linarith only [hp,hr]
  have hQ : 0 ≤ highExtractionEnergy v := by
    linarith only [highExtractionEnergy_lower v,normSq_nonneg v]
  have hQmax : highExtractionEnergy v ≤ 211722 := by
    exact high_extraction_membrane_energy v hv.1
  have hE : highExtractionEnergy (fun i => (x i-q*v i)-s i) =
      highExtractionEnergy y+q*(-2*highExtractionPair y v)+q^2*highExtractionEnergy v := by
    have hid : (fun i => (x i-q*v i)-s i)=(fun i => y i-q*v i) := by
      funext i
      dsimp [y]
      ring
    rw [hid,high_extraction_energy_sub]
    ring
  have h := membrane_observable_bound γ (N : ℝ) (m : ℝ) (x 2) r
    (highExtractionEnergy y) (highExtractionEnergy (fun i => (x i-q*v i)-s i))
    (-2*highExtractionPair y v) (highExtractionEnergy v) hγ hγmax (Nat.cast_nonneg N)
    (by exact_mod_cast hm) (by exact_mod_cast hNm) hz.1 hz.2 hrmax hL hQ hQmax hE
  rw [hsq] at h
  simpa only [energyExponential,y,v,q] using h


theorem high_extraction_growing_bound (rho z γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (he : extractDrift rho 0 (lift rho z) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N m : ℕ) (hm : 1 ≤ m) (hNm : N ≤ m) (n : Counts)
    (hy : ∀ i, |concentration m n i-lift rho z i| ≤ 1/400)
    (hnorm : normSq (fun i => concentration m n i-lift rho z i) ≤ 1/160000)
    (hx : ∀ i, |concentration m n i| ≤ 35)
    (hxz : 0 ≤ concentration m n 2 ∧ concentration m n 2 ≤ 4)
    (hs : ∀ i, lift rho z i ≤ 34) :
    extractGrowthGenerator rho γ m ((energyExponential highExtractionEnergy) N (lift rho z)) (concentration m n) ≤
      localAlpha*(energyExponential highExtractionEnergy) N (lift rho z) (concentration m n)*
        (-(N:ℝ)/4*normSq (fun i => concentration m n i-lift rho z i)+
          200000000+8000000000*(N:ℝ)*γ^2) := by
  have hres := high_extraction_resident_birth rho z hr hz he N m hm hNm n hy hs
  have hmem := high_extraction_membrane_bound γ N m (lift rho z)
    (concentration m n) hγ hγmax hm hNm hx hxz hnorm
  have hpos : 0 ≤ localAlpha*(energyExponential highExtractionEnergy) N (lift rho z) (concentration m n) := by
    unfold localAlpha energyExponential
    positivity
  unfold extractGrowthGenerator
  nlinarith only [hres,hmem,hpos]

end
end ProductiveMemory
