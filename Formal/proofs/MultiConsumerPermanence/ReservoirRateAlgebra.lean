import proofs.MultiConsumerPermanence.ReservoirRateSource
import proofs.MultiConsumerPermanence.RateLoadedPotential
import proofs.MultiConsumerPermanence.ReservoirPersistence

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence
open scoped BigOperators

theorem consumer_error_24 {n : ℕ} (r : Rates n) (delta z : ℝ)
    (hd : 0 ≤ delta) (hz : 0 ≤ z) (hz' : z ≤ 24)
    (hk : ∀ i, |r.k i-1| ≤ delta) (hm : ∀ i, |r.mu i-1/2| ≤ delta) (i : Fin n) :
    |(r.k i*z-r.mu i)-(z-1/2)| ≤ 25*delta := by
  obtain ⟨hkL,hkU⟩ := abs_le.mp (hk i)
  obtain ⟨hmL,hmU⟩ := abs_le.mp (hm i)
  have hL := mul_le_mul_of_nonneg_right hkL hz
  have hU := mul_le_mul_of_nonneg_right hkU hz
  have hdz := mul_le_mul_of_nonneg_left hz' hd
  apply abs_le.mpr
  constructor <;> nlinarith only [hL,hU,hmL,hmU,hdz]

theorem growth_total_bounds_24 {n : ℕ} (r : Rates n) (x : Fin n → ℝ) (z delta : ℝ)
    (hd : 0 ≤ delta) (hx : ∀ i, 0 ≤ x i) (hz : 0 ≤ z) (hz' : z ≤ 24)
    (hk : ∀ i, |r.k i-1| ≤ delta) (hm : ∀ i, |r.mu i-1/2| ≤ delta) :
    (z-1/2-25*delta)*total x ≤ growthTotal r z x ∧
      growthTotal r z x ≤ (z-1/2+25*delta)*total x := by
  have he := fun i => abs_le.mp (consumer_error_24 r delta z hd hz hz' hk hm i)
  constructor
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (show z-1/2-25*delta ≤ r.k i*z-r.mu i by linarith [(he i).1]) (hx i))
    simpa only [growthTotal,total,Finset.sum_mul,mul_comm] using hh
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (show r.k i*z-r.mu i ≤ z-1/2+25*delta by linarith [(he i).2]) (hx i))
    simpa only [growthTotal,total,Finset.sum_mul,mul_comm] using hh

theorem reservoir_feed_error (R feed wash d delta : ℝ)
    (hR : 0 ≤ R) (hR' : R ≤ 2) (hd : 0 ≤ delta)
    (hf : |feed-d| ≤ delta) (hw : |wash-d| ≤ delta) :
    |(R-1)*((feed-d)-(wash-d)*R)| ≤ 3*delta := by
  have hR1 : |R-1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hdiff : |(feed-d)-(wash-d)*R| ≤ 3*delta := by
    calc
      _ ≤ |feed-d|+|(wash-d)*R| := abs_sub _ _
      _ = |feed-d| + |wash-d| * R := by rw [abs_mul,abs_of_nonneg hR]
      _ ≤ delta+delta*R := add_le_add hf (mul_le_mul_of_nonneg_right hw hR)
      _ ≤ 3*delta := by nlinarith [mul_le_mul_of_nonneg_left hR' hd]
  rw [abs_mul]
  exact (mul_le_mul hR1 hdiff (abs_nonneg _) (by norm_num)).trans (by simp)

theorem reservoir_rate_phi_drift {n : ℕ} (r : ReservoirRates n) (x : Fin n → ℝ)
    (R z d dmin delta : ℝ) (hR : 0 ≤ R) (hR' : R ≤ 2)
    (hz : 0 ≤ z) (hz' : z ≤ 12) (hd : dmin ≤ d) (hdelta : 0 ≤ delta)
    (hx : ∀ i, 0 ≤ x i) (hK : 0 ≤ copyingLoad r.reactions x)
    (hk : ∀ i, |r.reactions.k i-1| ≤ delta)
    (hf : |r.feed-d| ≤ delta) (hw : |r.wash-d| ≤ delta) :
    (R-1)*(r.feed-r.wash*R-R*z*copyingLoad r.reactions x) ≤
      -dmin*(R-1)^2+3*(1+delta)*total x+3*delta := by
  have hh := reservoir_potential_drift R z (copyingLoad r.reactions x) d 12 hz hz' hK
  have he := (abs_le.mp (reservoir_feed_error R r.feed r.wash d delta hR hR' hdelta hf hw)).2
  have hdq := mul_le_mul_of_nonneg_right hd (sq_nonneg (R-1))
  have hload := copying_load_upper r.reactions x delta hx hk
  nlinarith only [hh,he,hdq,hload]

theorem reservoir_rate_corrected_growth {n : ℕ} (e d dmin delta : ℝ) (r : ReservoirRates n)
    (hr : ReservoirNear e d delta r) (hdmin : 0 < dmin) (hd : dmin ≤ d)
    (hdelta : 0 ≤ delta) (hdelta' : delta ≤ rateRadius)
    (hsmall : delta ≤ 1/(1000*(1+reservoirWeight dmin)))
    (A B z H R : ℝ) (x : Fin n → ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (hA : 0 ≤ A) (hA' : A ≤ 34) (hB : 2 ≤ B) (hB' : B ≤ 34)
    (hz : 0 ≤ z) (hz' : z ≤ 12) (hH : 0 ≤ H) (hH' : H ≤ 1536/7)
    (hR : 0 ≤ R) (hR' : R ≤ 2) (hx : ∀ i, 0 ≤ x i)
    (hK : 0 ≤ copyingLoad r.reactions x) :
    total x*(1/16-((n:ℝ)+120000002+6*reservoirWeight dmin)*total x) ≤
      growthTotal r.reactions (R*z) x-lossTotal r.reactions x-
        150000*total x*(ratePotentialRate e (baseRates r.reactions) A B z H
          (R*copyingLoad r.reactions x)+(reservoirWeight dmin/150000)*
          ((R-1)*(r.feed-r.wash*R-R*z*copyingLoad r.reactions x))) := by
  let D := dissipation (A+B-responseTotal e B) (60-(2+z)*B)
    (responseTotal e B-(1+z)*B-16*z-4*z^2+3*H) (16*z+2*z^2-(20001/10000)*H)
  let b := reservoirWeight dmin
  have hb : 0 ≤ b := by dsimp [b,reservoirWeight]; positivity
  have hS := total_nonneg x hx
  have hgap := corrected_boundary_growth z D hz (dissipation_nonneg _ _ _ _)
    (fun hlow => residual_gap _ _ _ _ (low_resource_separation e B z H he he' hB hB' hz hlow))
  have hv := consumer_potential_dissipation e A B z H (R*copyingLoad r.reactions x)
    he he' hA hA' hB hB' hz hz' hH hH' (mul_nonneg hR hK)
  have herr := (abs_le.mp (rate_loaded_potential_error e delta r.reactions hr.reactions hdelta'
    A B z H (R*copyingLoad r.reactions x) he he' hA hA' hB hB' hz hz' hH hH')).2
  have hload := mul_le_mul_of_nonneg_left (copying_load_upper r.reactions x delta hx hr.reactions.k) hR
  have hRS := mul_le_mul_of_nonneg_right hR' (mul_nonneg hdelta hS)
  have hv' : ratePotentialRate e (baseRates r.reactions) A B z H (R*copyingLoad r.reactions x)-
      1/10000000-800*delta*total x ≤ -D+400*R*total x := by
    dsimp [D]
    nlinarith only [hv,herr,hload,hRS]
  have hp := reservoir_rate_phi_drift r x R z d dmin delta hR hR' hz hz' hd hdelta hx hK
    hr.reactions.k hr.feed hr.wash
  have hp' : (R-1)*(r.feed-r.wash*R-R*z*copyingLoad r.reactions x)-3*delta-3*delta*total x ≤
      -dmin*(R-1)^2+(12/4)*total x := by linarith only [hp]
  have hbd : b*dmin = 2*(12:ℝ)^2 := by dsimp [b,reservoirWeight]; field_simp; norm_num
  have hc := reservoir_corrected_growth R z 12 (total x) D _ _ b dmin hR' hz hz' hS hb hbd hgap hv' hp'
  have hcs := mul_le_mul_of_nonneg_right hc hS
  have hRz : R*z ≤ 24 := by nlinarith [mul_le_mul_of_nonneg_right hR' hz]
  have hg := (growth_total_bounds_24 r.reactions x (R*z) delta hdelta hx (mul_nonneg hR hz)
    hRz hr.reactions.k hr.reactions.mu).1
  have hl := loss_total_upper r.reactions x delta hdelta hx hr.reactions.rho
  have hbdsmall : b*delta ≤ 1/1000 := by
    have hh := (le_div_iff₀ (show 0 < 1000*(1+b) by positivity)).1 hsmall
    nlinarith only [hh,hdelta]
  have hd1 : delta ≤ 1 := by dsimp [rateRadius] at hdelta'; linarith only [hdelta']
  have hlin : (1/16:ℝ) ≤ 1/8-150000/10000000-3*b*delta-25*delta := by
    dsimp [rateRadius] at hdelta'
    linarith only [hbdsmall,hdelta']
  have hquad : (n:ℝ)+delta+120000000+3*b+120000000*delta+3*b*delta ≤
      (n:ℝ)+120000002+6*b := by
    have hh := mul_le_mul_of_nonneg_left hd1 hb
    dsimp [rateRadius] at hdelta'
    nlinarith only [hh,hdelta']
  have hlinS := mul_le_mul_of_nonneg_right hlin hS
  have hquadS := mul_le_mul_of_nonneg_right hquad (sq_nonneg (total x))
  change total x*(1/16-((n:ℝ)+120000002+6*b)*total x) ≤ _
  nlinarith only [hcs,hg,hl,hlinS,hquadS]

end MultiConsumerPermanence
