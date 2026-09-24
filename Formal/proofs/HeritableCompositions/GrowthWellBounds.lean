import proofs.HeritableCompositions.LocalGrowingGenerator
import proofs.HeritableCompositions.GrowthDomains
import proofs.HeritableCompositions.EnvelopeTail
import proofs.FiniteCopy.WellExit

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

theorem small_growth_energy_geometry (m : ℕ) (n : Counts) (s : Point)
    (hs : ∀ i, s i ≤ 34) (hsz : s 2 ≤ 3) (E : Point → ℝ)
    (hE : ∀ y, (1/200)*normSq y ≤ E y)
    (he : E (fun i => concentration m n i-s i) < 1/32000000) :
    (∀ i, |concentration m n i-s i| ≤ 1/400) ∧
    normSq (fun i => concentration m n i-s i) ≤ 1/160000 ∧
    (∀ i, |concentration m n i| ≤ 35) ∧
    (0 ≤ concentration m n 2 ∧ concentration m n 2 ≤ 4) := by
  have hy := small_energy_coordinates E hE _ he
  have hx0 (i) : 0 ≤ concentration m n i := by unfold concentration; positivity
  refine ⟨hy,?_,?_,hx0 2,?_⟩
  · linarith only [hE (fun i => concentration m n i-s i),he]
  · intro i
    rw [abs_of_nonneg (hx0 i)]
    linarith only [(abs_le.mp (hy i)).2,hs i]
  · linarith only [(abs_le.mp (hy 2)).2,hsz]

theorem low_growth_local_ceiling (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hstationary : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N) (c : Compartment) (hNm : N ≤ c.2)
    (he : lowEnergy (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i) < 1/32000000) :
    compartmentGenerator γ
      (fun d => lowExponential N (pointOfState (lift sourceRates z)) (concentration d.2 d.1)) c ≤
      growingCeiling N γ := by
  have hm : 1 ≤ c.2 := hN.trans hNm
  have hsz : pointOfState (lift sourceRates z) 2 ≤ 3 := by
    change z ≤ 3
    linarith only [hz.2]
  have hg := small_growth_energy_geometry c.2 c.1 _ (lowroot_upper z hz) hsz
    lowEnergy lowEnergy_lower he
  have hlocal := low_growing_generator_bound z γ hz hstationary hγ hγmax N c.2 hm hNm c.1
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
  have hupper : lowEnergy (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i) ≤
      42*normSq (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i) := by
    nlinarith only [lowEnergy_upper (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i),
      normSq_nonneg (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i)]
  rw [compartment_generator_binding γ c.2 (by omega) c.1]
  exact hlocal.trans (growing_global_envelope N γ _ _ (Nat.cast_nonneg N) (normSq_nonneg _) hupper)

theorem high_growth_local_ceiling (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hstationary : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N) (c : Compartment) (hNm : N ≤ c.2)
    (he : highEnergy (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i) < 1/32000000) :
    compartmentGenerator γ
      (fun d => highExponential N (pointOfState (lift sourceRates z)) (concentration d.2 d.1)) c ≤
      growingCeiling N γ := by
  have hm : 1 ≤ c.2 := hN.trans hNm
  have hsz : pointOfState (lift sourceRates z) 2 ≤ 3 := by
    change z ≤ 3
    linarith only [hz.2]
  have hg := small_growth_energy_geometry c.2 c.1 _ (highroot_upper z hz) hsz
    highEnergy highEnergy_lower he
  have hlocal := high_growing_generator_bound z γ hz hstationary hγ hγmax N c.2 hm hNm c.1
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
  have hupper := highEnergy_upper (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i)
  simp only [div_one] at hupper
  rw [compartment_generator_binding γ c.2 (by omega) c.1]
  exact hlocal.trans (growing_global_envelope N γ _ _ (Nat.cast_nonneg N) (normSq_nonneg _) hupper)

end HeritableCompositions
