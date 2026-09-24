import proofs.MultiConsumerPermanence.RateBounds
import proofs.RobustPermanence.UniformPotential

namespace MultiConsumerPermanence
open CoreCouplingGlobal CoreCouplingCAC RobustPermanence Set

theorem rate_loaded_potential_hasDerivAt (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (r : AssemblyRates)
    (Y : ℝ → State) (K : ℝ → ℝ) (h : IsRateLoadedTrajectory r Y K)
    (t : ℝ) (ht : 0 ≤ t) (hB : (Y t).B ∈ Icc (2:ℝ) 34)
    (hz : (Y t).z ∈ Icc (0:ℝ) 12) (hH : (Y t).H ∈ Icc (0:ℝ) (1536/7)) :
    HasDerivAt (trajectoryPotential e p Y)
      (ratePotentialRate e r (Y t).A (Y t).B (Y t).z (Y t).H (K t)) t := by
  have dr := ((h.dA t ht).add (h.dB t ht)).sub
    ((responseTotal_hasDerivAt e (Y t).B he he' hB.1 hB.2).comp t (h.dB t ht))
  exact responsePotential_hasDerivAt e p he he'
    (fun t => (Y t).B) (fun t => (Y t).z) (fun t => (Y t).H)
    (fun t => (Y t).A+(Y t).B-responseTotal e (Y t).B) t _ _ _ _
    hB hz hH (h.dB t ht) (h.dz t ht) (h.dH t ht) dr

theorem rate_loaded_potential_error {n : ℕ} (e delta : ℝ) (r : Rates n)
    (hr : Near e delta r) (hd : delta ≤ rateRadius)
    (A B z H K : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (hA : 0 ≤ A) (hA' : A ≤ 34) (hB : 2 ≤ B) (hB' : B ≤ 34)
    (hz : 0 ≤ z) (hz' : z ≤ 12) (hH : 0 ≤ H) (hH' : H ≤ 1536/7) :
    |ratePotentialRate e (baseRates r) A B z H K-potentialRate e A B z H K| ≤ 1/10000000 := by
  obtain ⟨ha,hb,hzz,hh,_⟩ := rate_resident_errors e (baseRates r) (near_base e delta r hr hd)
    A B z H 0 hA hA' (by linarith) hB' hz hz' hH hH' (by norm_num) (by norm_num)
  have hp := small_potential_direction e A B z H
    (rateA (baseRates r) A B z-fA (flagshipRates e) A B z)
    (rateB (baseRates r) A B z-fB (flagshipRates e) A B z)
    (rateZ (baseRates r) A B z H 0-(fZ (flagshipRates e) A B z H-z*0))
    (rateH (baseRates r) z H-fH (flagshipRates e) z H)
    he he' hA hA' hB hB' hz hz' hH hH' ha hb hzz hh
  have hid : potentialDirection e A B z H
      (rateA (baseRates r) A B z-fA (flagshipRates e) A B z)
      (rateB (baseRates r) A B z-fB (flagshipRates e) A B z)
      (rateZ (baseRates r) A B z H 0-(fZ (flagshipRates e) A B z H-z*0))
      (rateH (baseRates r) z H-fH (flagshipRates e) z H) =
      ratePotentialRate e (baseRates r) A B z H K-potentialRate e A B z H K := by
    dsimp [potentialDirection,ratePotentialRate,potentialRate,rateZ,baseRates]
    ring
  rwa [hid] at hp

theorem perturbed_corrected_growth {n : ℕ} (e delta : ℝ) (r : Rates n)
    (hr : Near e delta r) (hd : 0 ≤ delta) (hd' : delta ≤ rateRadius)
    (A B z H : ℝ) (x : Fin n → ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (hA : 0 ≤ A) (hA' : A ≤ 34) (hB : 2 ≤ B) (hB' : B ≤ 34)
    (hz : 0 ≤ z) (hz' : z ≤ 12) (hH : 0 ≤ H) (hH' : H ≤ 1536/7)
    (hx : ∀ i, 0 ≤ x i) (hK : 0 ≤ copyingLoad r x) :
    total x*(1/8-((n:ℝ)+60000001)*total x) ≤
      growthTotal r z x-lossTotal r x-
        150000*total x*ratePotentialRate e (baseRates r) A B z H (copyingLoad r x) := by
  let D := dissipation (A+B-responseTotal e B) (60-(2+z)*B)
    (responseTotal e B-(1+z)*B-16*z-4*z^2+3*H)
    (16*z+2*z^2-(20001/10000)*H)
  have hD : 0 ≤ D := dissipation_nonneg _ _ _ _
  have hgap : z ≤ 3/4 → 529/103640000 ≤ D := by
    intro hlow
    exact residual_gap _ _ _ _ (low_resource_separation e B z H he he' hB hB' hz hlow)
  have hgapS := mul_le_mul_of_nonneg_right (corrected_boundary_growth z D hz hD hgap)
    (total_nonneg x hx)
  have hV := consumer_potential_dissipation e A B z H (copyingLoad r x)
    he he' hA hA' hB hB' hz hz' hH hH' hK
  have herr := (abs_le.mp (rate_loaded_potential_error e delta r hr hd' A B z H (copyingLoad r x)
    he he' hA hA' hB hB' hz hz' hH hH')).2
  have hload := copying_load_upper r x delta hx hr.k
  have hV' : ratePotentialRate e (baseRates r) A B z H (copyingLoad r x) ≤
      -D+400*(1+delta)*total x+1/10000000 := by
    change potentialRate e A B z H (copyingLoad r x) ≤ -D+400*copyingLoad r x at hV
    linarith only [hV,herr,hload]
  have hVS := mul_le_mul_of_nonneg_left hV'
    (show 0 ≤ 150000*total x from mul_nonneg (by norm_num) (total_nonneg x hx))
  have hg := (growth_total_bounds r x z delta hd hx hz hz' hr.k hr.mu).1
  have hl := loss_total_upper r x delta hd hx hr.rho
  have hlin : (1/8:ℝ) ≤ 1/4-13*delta-150000/10000000 := by
    dsimp [rateRadius] at hd'
    linarith only [hd']
  have hquad : (n:ℝ)+delta+60000000*(1+delta) ≤ (n:ℝ)+60000001 := by
    dsimp [rateRadius] at hd'
    linarith only [hd']
  have hlinS := mul_le_mul_of_nonneg_right hlin (total_nonneg x hx)
  have hquadS := mul_le_mul_of_nonneg_right hquad (sq_nonneg (total x))
  nlinarith only [hgapS,hVS,hg,hl,hlinS,hquadS]

end MultiConsumerPermanence
