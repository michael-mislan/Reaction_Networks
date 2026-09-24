import proofs.HeritableCompositions.ResidentScaling
import proofs.HeritableCompositions.MembraneNoise
import proofs.HeritableCompositions.SourceRecovery

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

theorem low_resident_birth_bound (z : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (N m : ℕ) (hm : 1 ≤ m) (hNm : N ≤ m) (n : Counts)
    (hy : ∀ i, |concentration m n i-pointOfState (lift sourceRates z) i| ≤ 1/400) :
    generator (1/100000) m (lowExponential N (pointOfState (lift sourceRates z)))
      (concentration m n) ≤
      localAlpha*lowExponential N (pointOfState (lift sourceRates z)) (concentration m n)*
        (-(N : ℝ)/2*normSq (fun i => concentration m n i-pointOfState (lift sourceRates z) i)+100000000) := by
  let s := pointOfState (lift sourceRates z)
  let E := fun x : Point => lowEnergy (fun i => x i-s i)
  have hsource := lowlocal_generator z hz hs m hm n hy
  unfold lowExponential at hsource ⊢
  have h := source_scaled_dissipation (1/100000) localAlpha
    (normSq (fun i => concentration m n i-s i)) 100000000 (by norm_num)
    (by norm_num [localAlpha]) (by norm_num) N m hm hNm n E
    (by simpa only [E,s,mul_assoc,mul_left_comm,mul_comm] using hsource)
  simpa only [E,s,mul_assoc,mul_left_comm,mul_comm] using h

theorem high_resident_birth_bound (z : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (N m : ℕ) (hm : 1 ≤ m) (hNm : N ≤ m) (n : Counts)
    (hy : ∀ i, |concentration m n i-pointOfState (lift sourceRates z) i| ≤ 1/400) :
    generator (1/100000) m (highExponential N (pointOfState (lift sourceRates z)))
      (concentration m n) ≤
      localAlpha*highExponential N (pointOfState (lift sourceRates z)) (concentration m n)*
        (-(N : ℝ)/2*normSq (fun i => concentration m n i-pointOfState (lift sourceRates z) i)+100000000) := by
  let s := pointOfState (lift sourceRates z)
  let E := fun x : Point => highEnergy (fun i => x i-s i)
  have hsource := highlocal_generator z hz hs m hm n hy
  unfold highExponential at hsource ⊢
  have h := source_scaled_dissipation (1/100000) localAlpha
    (normSq (fun i => concentration m n i-s i)) 100000000 (by norm_num)
    (by norm_num [localAlpha]) (by norm_num) N m hm hNm n E
    (by simpa only [E,s,mul_assoc,mul_left_comm,mul_comm] using hsource)
  simpa only [E,s,mul_assoc,mul_left_comm,mul_comm] using h

theorem low_energy_sub_scaled (y v : Point) (q : ℝ) :
    lowEnergy (fun i => y i-q*v i) = lowEnergy y-2*q*lowPair y v+q^2*lowEnergy v := by
  unfold lowEnergy lowPair
  ring

theorem high_energy_sub_scaled (y v : Point) (q : ℝ) :
    highEnergy (fun i => y i-q*v i) = highEnergy y-2*q*highPair y v+q^2*highEnergy v := by
  unfold highEnergy highPair
  ring

end HeritableCompositions
