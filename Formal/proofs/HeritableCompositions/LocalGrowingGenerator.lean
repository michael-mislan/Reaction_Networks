import proofs.HeritableCompositions.GrowthEnergy

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

theorem low_membrane_observable_bound (γ : ℝ) (N m : ℕ) (s x : Point)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000) (hm : 1 ≤ m) (hNm : N ≤ m)
    (hx : ∀ i, |x i| ≤ 35) (hz : 0 ≤ x 2 ∧ x 2 ≤ 4)
    (hy : normSq (fun i => x i-s i) ≤ 1/160000) :
    γ*(m : ℝ)*x 2*(lowExponential N s
      (fun i => x i-(1/((m : ℝ)+1))*(x i+membraneDirection i))-lowExponential N s x) ≤
    localAlpha*lowExponential N s x*
      ((N : ℝ)*normSq (fun i => x i-s i)/4+8000000000*(N : ℝ)*γ^2+1) := by
  let y : Point := fun i => x i-s i
  let v : Point := fun i => x i+membraneDirection i
  let q : ℝ := 1/((m : ℝ)+1)
  let r := Real.sqrt (normSq y)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hsq : r^2=normSq y := Real.sq_sqrt (normSq_nonneg y)
  have hrmax : r ≤ 1/400 := by nlinarith only [hsq,hr,hy]
  have hv := membrane_vector_bounds x hx
  have hp := low_pair_box_bound y v r hr (coordinate_le_radius y) hv.1
  have hL : |-2*lowPair y v| ≤ 14400*r := by
    rw [abs_mul]
    norm_num
    linarith only [hp]
  have hQ : 0 ≤ lowEnergy v := by
    linarith only [lowEnergy_lower v,normSq_nonneg v]
  have hQmax : lowEnergy v ≤ 211722 := by
    have hv' : normSq v ≤ 5041 := hv.2
    linarith only [lowEnergy_upper v,hv']
  have hE : lowEnergy (fun i => (x i-q*v i)-s i) =
      lowEnergy y+q*(-2*lowPair y v)+q^2*lowEnergy v := by
    have hid : (fun i => (x i-q*v i)-s i)=(fun i => y i-q*v i) := by
      funext i
      dsimp [y]
      ring
    rw [hid,low_energy_sub_scaled]
    ring
  have h := membrane_observable_bound γ (N : ℝ) (m : ℝ) (x 2) r
    (lowEnergy y) (lowEnergy (fun i => (x i-q*v i)-s i))
    (-2*lowPair y v) (lowEnergy v) hγ hγmax (Nat.cast_nonneg N)
    (by exact_mod_cast hm) (by exact_mod_cast hNm) hz.1 hz.2 hrmax hL hQ hQmax hE
  rw [hsq] at h
  simpa only [lowExponential,y,v,q] using h

theorem low_growing_generator_bound (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N m : ℕ) (hm : 1 ≤ m) (hNm : N ≤ m) (n : Counts)
    (hy : ∀ i, |concentration m n i-pointOfState (lift sourceRates z) i| ≤ 1/400)
    (hnorm : normSq (fun i => concentration m n i-pointOfState (lift sourceRates z) i) ≤ 1/160000)
    (hx : ∀ i, |concentration m n i| ≤ 35)
    (hxz : 0 ≤ concentration m n 2 ∧ concentration m n 2 ≤ 4) :
    growthGenerator γ m (lowExponential N (pointOfState (lift sourceRates z))) (concentration m n) ≤
      localAlpha*lowExponential N (pointOfState (lift sourceRates z)) (concentration m n)*
        (-(N : ℝ)/4*normSq (fun i => concentration m n i-pointOfState (lift sourceRates z) i)+
          200000000+8000000000*(N : ℝ)*γ^2) := by
  have hres := low_resident_birth_bound z hz hs N m hm hNm n hy
  have hmem := low_membrane_observable_bound γ N m (pointOfState (lift sourceRates z))
    (concentration m n) hγ hγmax hm hNm hx hxz hnorm
  have hpos : 0 ≤ localAlpha*lowExponential N (pointOfState (lift sourceRates z)) (concentration m n) := by
    unfold localAlpha lowExponential
    positivity
  unfold growthGenerator
  nlinarith only [hres,hmem,hpos]

theorem high_membrane_observable_bound (γ : ℝ) (N m : ℕ) (s x : Point)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000) (hm : 1 ≤ m) (hNm : N ≤ m)
    (hx : ∀ i, |x i| ≤ 35) (hz : 0 ≤ x 2 ∧ x 2 ≤ 4)
    (hy : normSq (fun i => x i-s i) ≤ 1/160000) :
    γ*(m : ℝ)*x 2*(highExponential N s
      (fun i => x i-(1/((m : ℝ)+1))*(x i+membraneDirection i))-highExponential N s x) ≤
    localAlpha*highExponential N s x*
      ((N : ℝ)*normSq (fun i => x i-s i)/4+8000000000*(N : ℝ)*γ^2+1) := by
  let y : Point := fun i => x i-s i
  let v : Point := fun i => x i+membraneDirection i
  let q : ℝ := 1/((m : ℝ)+1)
  let r := Real.sqrt (normSq y)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hsq : r^2=normSq y := Real.sq_sqrt (normSq_nonneg y)
  have hrmax : r ≤ 1/400 := by nlinarith only [hsq,hr,hy]
  have hv := membrane_vector_bounds x hx
  have hp := high_pair_box_bound y v r hr (coordinate_le_radius y) hv.1
  have hL : |-2*highPair y v| ≤ 14400*r := by
    rw [abs_mul]
    norm_num
    linarith only [hp]
  have hQ : 0 ≤ highEnergy v := by
    linarith only [highEnergy_lower v,normSq_nonneg v]
  have hQmax : highEnergy v ≤ 211722 := by
    have hv' : normSq v ≤ 5041 := hv.2
    linarith only [highEnergy_upper v,hv']
  have hE : highEnergy (fun i => (x i-q*v i)-s i) =
      highEnergy y+q*(-2*highPair y v)+q^2*highEnergy v := by
    have hid : (fun i => (x i-q*v i)-s i)=(fun i => y i-q*v i) := by
      funext i
      dsimp [y]
      ring
    rw [hid,high_energy_sub_scaled]
    ring
  have h := membrane_observable_bound γ (N : ℝ) (m : ℝ) (x 2) r
    (highEnergy y) (highEnergy (fun i => (x i-q*v i)-s i))
    (-2*highPair y v) (highEnergy v) hγ hγmax (Nat.cast_nonneg N)
    (by exact_mod_cast hm) (by exact_mod_cast hNm) hz.1 hz.2 hrmax hL hQ hQmax hE
  rw [hsq] at h
  simpa only [highExponential,y,v,q] using h

theorem high_growing_generator_bound (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N m : ℕ) (hm : 1 ≤ m) (hNm : N ≤ m) (n : Counts)
    (hy : ∀ i, |concentration m n i-pointOfState (lift sourceRates z) i| ≤ 1/400)
    (hnorm : normSq (fun i => concentration m n i-pointOfState (lift sourceRates z) i) ≤ 1/160000)
    (hx : ∀ i, |concentration m n i| ≤ 35)
    (hxz : 0 ≤ concentration m n 2 ∧ concentration m n 2 ≤ 4) :
    growthGenerator γ m (highExponential N (pointOfState (lift sourceRates z))) (concentration m n) ≤
      localAlpha*highExponential N (pointOfState (lift sourceRates z)) (concentration m n)*
        (-(N : ℝ)/4*normSq (fun i => concentration m n i-pointOfState (lift sourceRates z) i)+
          200000000+8000000000*(N : ℝ)*γ^2) := by
  have hres := high_resident_birth_bound z hz hs N m hm hNm n hy
  have hmem := high_membrane_observable_bound γ N m (pointOfState (lift sourceRates z))
    (concentration m n) hγ hγmax hm hNm hx hxz hnorm
  have hpos : 0 ≤ localAlpha*highExponential N (pointOfState (lift sourceRates z)) (concentration m n) := by
    unfold localAlpha highExponential
    positivity
  unfold growthGenerator
  nlinarith only [hres,hmem,hpos]

end HeritableCompositions
