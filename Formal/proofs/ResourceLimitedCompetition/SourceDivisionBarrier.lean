import proofs.ResourceLimitedCompetition.DivisionBarrier

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

theorem source_growth_ratio (E : Point → ℝ) (P : Point → Point → ℝ)
    (hquad : ∀ y v q, E (fun i => y i-q*v i)=E y-2*q*P y v+q^2*E v)
    (hlower : ∀ y, (1/200)*normSq y ≤ E y)
    (hupper : ∀ y, E y ≤ 42*normSq y)
    (hpair : ∀ y v r, 0 ≤ r → (∀ i, |y i| ≤ r) → (∀ i, |v i| ≤ 36) → |P y v| ≤ 7200*r)
    (s : Point) (hs : ∀ i, s i ≤ 34) (hsz : s 2 ≤ 3)
    (N : ℕ) (hN : 1 ≤ N) (c : Compartment) (hNm : N ≤ c.2) (hn : 1 ≤ c.1 2)
    (he : E (fun i => concentration c.2 c.1 i-s i) < 1/32000000) :
    Real.exp ((N : ℝ)*localAlpha*E (fun i =>
      concentration (nextCompartment c (.inr ())).2 (nextCompartment c (.inr ())).1 i-s i)) ≤
      2*Real.exp ((N : ℝ)*localAlpha*E (fun i => concentration c.2 c.1 i-s i)) := by
  let x := concentration c.2 c.1
  let y : Point := fun i => x i-s i
  let v : Point := fun i => x i+membraneDirection i
  let q : ℝ := 1/((c.2 : ℝ)+1)
  have hg := small_growth_energy_geometry c.2 c.1 s hs hsz E hlower he
  have hv := membrane_vector_bounds x hg.2.2.1
  have hp := hpair y v (1/400) (by norm_num) hg.1 hv.1
  have hL : -2*P y v ≤ 36 := by linarith only [(abs_le.mp hp).1]
  have hQ : 0 ≤ E v := by linarith only [hlower v,normSq_nonneg v]
  have hQmax : E v ≤ 211722 := by linarith only [hupper v,hv.2]
  have hj : (fun i => concentration (nextCompartment c (.inr ())).2
      (nextCompartment c (.inr ())).1 i-s i) = (fun i => y i-q*v i) := by
    funext i
    have h := membrane_concentration_update c (by omega) hn i
    dsimp [y,q,v,x]
    rw [eq_add_of_sub_eq h]
    ring
  rw [hj]
  apply membrane_exponential_ratio (N : ℝ) (c.2 : ℝ) (E y)
    (E (fun i => y i-q*v i)) (-2*P y v) (E v)
    (Nat.cast_nonneg _) (by exact_mod_cast (hN.trans hNm)) (by exact_mod_cast hNm) hL hQ hQmax
  rw [hquad]
  dsimp [q]
  ring

theorem low_source_growth_ratio (z : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (N : ℕ) (hN : 1 ≤ N) (c : Compartment) (hNm : N ≤ c.2) (hn : 1 ≤ c.1 2)
    (he : lowEnergy (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i) < 1/32000000) :
    lowExponential N (pointOfState (lift sourceRates z))
      (concentration (nextCompartment c (.inr ())).2 (nextCompartment c (.inr ())).1) ≤
      2*lowExponential N (pointOfState (lift sourceRates z)) (concentration c.2 c.1) := by
  apply source_growth_ratio lowEnergy lowPair low_energy_sub_scaled lowEnergy_lower
    (fun y => (lowEnergy_upper y).trans (by nlinarith only [normSq_nonneg y]))
    low_pair_box_bound _ (lowroot_upper z hz) _ N hN c hNm hn he
  change z ≤ 3
  linarith only [hz.2]

theorem high_source_growth_ratio (z : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (N : ℕ) (hN : 1 ≤ N) (c : Compartment) (hNm : N ≤ c.2) (hn : 1 ≤ c.1 2)
    (he : highEnergy (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i) < 1/32000000) :
    highExponential N (pointOfState (lift sourceRates z))
      (concentration (nextCompartment c (.inr ())).2 (nextCompartment c (.inr ())).1) ≤
      2*highExponential N (pointOfState (lift sourceRates z)) (concentration c.2 c.1) := by
  apply source_growth_ratio highEnergy highPair high_energy_sub_scaled highEnergy_lower
    (fun y => by simpa only [div_one] using highEnergy_upper y)
    high_pair_box_bound _ (highroot_upper z hz) _ N hN c hNm hn he
  change z ≤ 3
  linarith only [hz.2]

/-- Product barrier derived from the chemical affine drift and literal growth rate. -/
theorem compartment_spatial_bound (β : ℝ) (hβ : 0 ≤ β)
    (hβmax : β ≤ 1/100000000000) (N : ℕ) (c : Compartment)
    (hm : 0 < c.2) (hmmax : c.2 ≤ 2*N)
    (hz : concentration c.2 c.1 2 ≤ 4)
    (f : Compartment → ℝ) (hf : ∀ d, 0 ≤ f d)
    (hratio : f (nextCompartment c (.inr ())) ≤ 2*f c)
    (hgen : compartmentGenerator β f c ≤
      -((N : ℝ)*localAlpha*innerEnergy/672)*f c+
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2))) :
    compartmentGenerator β (fun d => spatialWeight (1/1000000000000000) N d.2*f d) c ≤
      -(((N : ℝ)*localAlpha*innerEnergy/672)/2)*
        (spatialWeight (1/1000000000000000) N c.2*f c)+
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  rw [spatial_generator_identity]
  have hmR : (0 : ℝ) < c.2 := by exact_mod_cast hm
  have hcount : (c.1 2 : ℝ) ≤ 8*(N : ℝ) := by
    have h := (div_le_iff₀ hmR).mp hz
    have hmax : (c.2 : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hmmax
    linarith only [h,hmax]
  have hrate : β*(c.1 2 : ℝ) ≤ 8*β*(N : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hcount hβ
    nlinarith only [h]
  have hg : spatialWeight (1/1000000000000000) N c.2 ≤ 1 := by
    unfold spatialWeight
    apply Real.exp_le_one_iff.mpr
    have hmax : (c.2 : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hmmax
    linarith only [hmax]
  exact spatial_barrier_drift β (1/1000000000000000) (β*(c.1 2 : ℝ)) (N : ℝ)
    ((N : ℝ)*localAlpha*innerEnergy/672) (f c) (f (nextCompartment c (.inr ())))
    (spatialWeight (1/1000000000000000) N c.2)
    (2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) (compartmentGenerator β f c)
    (Nat.cast_nonneg _) hβmax rfl (by positivity) hrate (hf c) (hf _) hratio
    (Real.exp_pos _).le hg (by positivity) rfl hgen

end ResourceLimitedCompetition
