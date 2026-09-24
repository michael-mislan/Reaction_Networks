import proofs.CompositionalMemory.EffectiveResident
import proofs.HeritableCompositions.ExponentialScaling

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set

theorem effective_scaled_dissipation (e α N m v B : ℝ)
    (he : 0 ≤ e) (hα : 0 ≤ α) (hN : 0 ≤ N) (hm : 0 < m)
    (hNm : N ≤ m) (hB : 0 ≤ B) (n : Counts) (E : Point → ℝ)
    (hsource : effectiveGenerator e m (fun x => Real.exp (m*(α*E x)))
      (effectiveConcentration m n) ≤ Real.exp (m*(α*E (effectiveConcentration m n)))*
        (α*(-m/2*v+B))) :
    effectiveGenerator e m (fun x => Real.exp (N*(α*E x)))
      (effectiveConcentration m n) ≤ Real.exp (N*(α*E (effectiveConcentration m n)))*
        (α*(-N/2*v+B)) := by
  let x := effectiveConcentration m n
  let c := (N/m)*Real.exp ((N-m)*(α*E x))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpoint (j : Fin 13) :
      densityRates e (1/m) x j*(Real.exp (N*(α*E (fun i => x i+jump j i/m)))-
        Real.exp (N*(α*E x))) ≤
      c*(densityRates e (1/m) x j*(Real.exp (m*(α*E (fun i => x i+jump j i/m)))-
        Real.exp (m*(α*E x)))) := by
    have hh := mul_le_mul_of_nonneg_left
      (HeritableCompositions.exp_two_scale_increment N m (α*E x)
        (α*E (fun i => x i+jump j i/m)) hN hm hNm)
      (effective_rates_nonneg e he m hm.le n j)
    dsimp [c]
    nlinarith only [hh]
  have hsum := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint j)) hm.le
  rw [← Finset.mul_sum] at hsum
  have hg : effectiveGenerator e m (fun x => Real.exp (N*(α*E x))) x ≤
      c*effectiveGenerator e m (fun x => Real.exp (m*(α*E x))) x := by
    unfold effectiveGenerator
    nlinarith only [hsum]
  have hs := mul_le_mul_of_nonneg_left hsource hc
  have hid : c*(Real.exp (m*(α*E x))*(α*(-m/2*v+B))) =
      Real.exp (N*(α*E x))*(α*(-N/2*v+B*(N/m))) := by
    dsimp [c]
    have hex : Real.exp ((N-m)*(α*E x))*Real.exp (m*(α*E x)) =
        Real.exp (N*(α*E x)) := by rw [← Real.exp_add]; congr 1; ring
    calc
      _ = (N/m)*(Real.exp ((N-m)*(α*E x))*Real.exp (m*(α*E x)))*
          (α*(-m/2*v+B)) := by ring
      _ = _ := by rw [hex]; field_simp
  have hratio : N/m ≤ 1 := (div_le_one hm).mpr hNm
  have hconst := mul_le_mul_of_nonneg_left hratio hB
  have hfinal : Real.exp (N*(α*E x))*(α*(-N/2*v+B*(N/m))) ≤
      Real.exp (N*(α*E x))*(α*(-N/2*v+B)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ hα
    linarith only [hconst]
  exact (hg.trans hs).trans (hid.le.trans hfinal)

theorem low_effective_birth_bound (z N m : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (hN : 0 ≤ N) (hm : 1 ≤ m) (hNm : N ≤ m) (n : Counts)
    (hy : ∀ i, |effectiveConcentration m n i-pointOfState (lift sourceRates z) i| ≤ 1/400) :
    effectiveGenerator (1/100000) m (lowVolumeExponential N (pointOfState (lift sourceRates z)))
      (effectiveConcentration m n) ≤
      localAlpha*lowVolumeExponential N (pointOfState (lift sourceRates z)) (effectiveConcentration m n)*
        (-N/2*normSq (fun i => effectiveConcentration m n i-pointOfState (lift sourceRates z) i)+100000000) := by
  have hsource := low_real_volume_generator z hz hs m hm n hy
  unfold lowVolumeExponential at hsource ⊢
  have h := effective_scaled_dissipation (1/100000) localAlpha N m
    (normSq (fun i => effectiveConcentration m n i-pointOfState (lift sourceRates z) i))
    100000000 (by norm_num) (by norm_num [localAlpha]) hN (by linarith) hNm (by norm_num) n
    (fun x => lowEnergy (fun i => x i-pointOfState (lift sourceRates z) i))
    (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hsource)
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h

theorem high_effective_birth_bound (z N m : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (hN : 0 ≤ N) (hm : 1 ≤ m) (hNm : N ≤ m) (n : Counts)
    (hy : ∀ i, |effectiveConcentration m n i-pointOfState (lift sourceRates z) i| ≤ 1/400) :
    effectiveGenerator (1/100000) m (highVolumeExponential N (pointOfState (lift sourceRates z)))
      (effectiveConcentration m n) ≤
      localAlpha*highVolumeExponential N (pointOfState (lift sourceRates z)) (effectiveConcentration m n)*
        (-N/2*normSq (fun i => effectiveConcentration m n i-pointOfState (lift sourceRates z) i)+100000000) := by
  have hsource := high_real_volume_generator z hz hs m hm n hy
  unfold highVolumeExponential at hsource ⊢
  have h := effective_scaled_dissipation (1/100000) localAlpha N m
    (normSq (fun i => effectiveConcentration m n i-pointOfState (lift sourceRates z) i))
    100000000 (by norm_num) (by norm_num [localAlpha]) hN (by linarith) hNm (by norm_num) n
    (fun x => highEnergy (fun i => x i-pointOfState (lift sourceRates z) i))
    (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hsource)
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h

end CompositionalMemory
