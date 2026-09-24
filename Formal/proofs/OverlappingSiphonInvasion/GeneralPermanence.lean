import proofs.OverlappingSiphonInvasion.PhysicalTrajectoryFloor
import proofs.OverlappingSiphonInvasion.RecoveryAlgebra

noncomputable section
open Filter Topology
namespace OverlappingSiphonInvasion

/-- Uniform permanence of every positive trajectory of the fourteen-reaction
source at arbitrary positive rates with both residents present and invading. -/
theorem general_trajectory_permanence (p : Rates) (hp : PositiveRates p)
    (he1 : p.mu1/p.alpha1 < p.recruitment/p.mu0)
    (he2 : p.mu2/p.alpha2 < p.recruitment/p.mu0) (hi : StrictMutualInvasion p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ X : ℝ → State, IsTrajectory p X →
      ∀ᶠ t in atTop, ∀ i, ε ≤ X t i ∧ X t i ≤ p.recruitment/deathFloor p+1 := by
  have hΛ : 0 < p.recruitment := by simpa [rateVector] using hp 0
  have hα1 : 0 < p.alpha1 := by simpa [rateVector] using hp 1
  have hα2 : 0 < p.alpha2 := by simpa [rateVector] using hp 2
  have hα3 : 0 < p.alpha3 := by simpa [rateVector] using hp 3
  have hη1 : 0 < p.eta1 := by simpa [rateVector] using hp 4
  have hη2 : 0 < p.eta2 := by simpa [rateVector] using hp 5
  have hγ1 : 0 < p.gamma1 := by simpa [rateVector] using hp 6
  have hγ2 : 0 < p.gamma2 := by simpa [rateVector] using hp 7
  have hβ1 : 0 < p.beta1 := by simpa [rateVector] using hp 8
  have hβ2 : 0 < p.beta2 := by simpa [rateVector] using hp 9
  have hμ0 : 0 < p.mu0 := by simpa [rateVector] using hp 10
  have hμ1 : 0 < p.mu1 := by simpa [rateVector] using hp 11
  have hμ2 : 0 < p.mu2 := by simpa [rateVector] using hp 12
  have hμ3 : 0 < p.mu3 := by simpa [rateVector] using hp 13
  have hm := deathFloor_pos p hp
  let R := p.recruitment/deathFloor p+1
  have hR : 0 < R := by dsimp [R]; positivity
  let q := coordinateLoss p R 0
  have hq : 0 < q := by dsimp [q,coordinateLoss]; positivity
  let l := (p.recruitment/q)/2
  have hl : 0 < l := by dsimp [l]; positivity
  obtain ⟨ru,rv,rj,k,δ,hru,hrv,hrj,_hk,hδ,hprod⟩ := source_trajectory_product_floor p hp he1 he2 hi
  let mU := δ/(((1+rv)*R)*(((2+rj)*R)^k))
  let mV := δ/(((1+ru)*R)*(((2+rj)*R)^k))
  have hmU : 0 < mU := by dsimp [mU]; positivity
  have hmV : 0 < mV := by dsimp [mV]; positivity
  let Ca := p.beta1*l*mU/ru
  let Cb := p.beta2*l*mV/rv
  let Ka := p.mu1+(p.gamma1+p.eta1)*R+p.beta1*l/ru
  let Kb := p.mu2+(p.gamma2+p.eta2)*R+p.beta2*l/rv
  have hCa : 0 < Ca := by dsimp [Ca]; positivity
  have hCb : 0 < Cb := by dsimp [Cb]; positivity
  have hKa : 0 < Ka := by dsimp [Ka]; positivity
  have hKb : 0 < Kb := by dsimp [Kb]; positivity
  let a0 := (Ca/Ka)/2
  let b0 := (Cb/Kb)/2
  have ha0 : 0 < a0 := by dsimp [a0]; positivity
  have hb0 : 0 < b0 := by dsimp [b0]; positivity
  let Cc := (p.gamma1+p.gamma2)*a0*b0
  have hCc : 0 < Cc := by dsimp [Cc]; positivity
  let c0 := (Cc/p.mu3)/2
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  let ε := min l (min a0 (min b0 c0))
  have hε : 0 < ε := lt_min hl (lt_min ha0 (lt_min hb0 hc0))
  refine ⟨ε,hε,?_⟩
  intro X hX
  have hbox : ∀ᶠ t in atTop, X t ∈ populationBox R := by
    filter_upwards [general_eventual_total_upper p hp X hX,eventually_ge_atTop (0:ℝ)] with t ht ht0
    exact ⟨fun i => (hX.positive t ht0 i).le,ht.le⟩
  obtain ⟨T1,hT1⟩ := eventually_atTop.1 (hbox.and (eventually_ge_atTop (0:ℝ)))
  have hs := lower_of_linear (fun t => X t 0) (fun t => field p (X t) 0)
    T1 p.recruitment q l hq (by dsimp [l]; linarith [div_pos hΛ hq])
    (fun t ht => hX.derivative t (hT1 t ht).2 0)
    (fun t ht => source_susceptible_lower p hp R (X t) (hT1 t ht).1)
  obtain ⟨T2,hT2⟩ := eventually_atTop.1
    ((hs.and hbox).and ((hprod X hX).and (eventually_ge_atTop (0:ℝ))))
  have hforce : ∀ t, T2 ≤ t →
      Ca-Ka*X t 1 ≤ field p (X t) 1 ∧ Cb-Kb*X t 2 ≤ field p (X t) 2 := by
    intro t ht
    have hh := hT2 t ht
    have hx := hX.positive t hh.2.2
    have hmass := product_to_mass_floors ru rv rj R δ k hru hrv hrj hR (X t) hh.1.2 hh.2.1
    constructor
    · simpa only [Ca,Ka,field] using private_mass_forcing p.alpha1 p.beta1 p.gamma1 p.eta1 p.mu1
        (X t 0) (X t 1) (X t 2) (X t 3) R l mU ru hα1.le hβ1.le hγ1.le hη1.le
        hru hl.le hh.1.1.le (hx 1).le (hx 3).le
        (populationBox_coordinate_le R (X t) hh.1.2 2)
        (populationBox_coordinate_le R (X t) hh.1.2 3) hmass.1
    · simpa only [Cb,Kb,field] using private_mass_forcing p.alpha2 p.beta2 p.gamma2 p.eta2 p.mu2
        (X t 0) (X t 2) (X t 1) (X t 3) R l mV rv hα2.le hβ2.le hγ2.le hη2.le
        hrv hl.le hh.1.1.le (hx 2).le (hx 3).le
        (populationBox_coordinate_le R (X t) hh.1.2 1)
        (populationBox_coordinate_le R (X t) hh.1.2 3) hmass.2
  have ha := lower_of_linear (fun t => X t 1) (fun t => field p (X t) 1) T2 Ca Ka a0 hKa
    (by dsimp [a0]; linarith [div_pos hCa hKa])
    (fun t ht => hX.derivative t (hT2 t ht).2.2 1) (fun t ht => (hforce t ht).1)
  have hb := lower_of_linear (fun t => X t 2) (fun t => field p (X t) 2) T2 Cb Kb b0 hKb
    (by dsimp [b0]; linarith [div_pos hCb hKb])
    (fun t ht => hX.derivative t (hT2 t ht).2.2 2) (fun t ht => (hforce t ht).2)
  obtain ⟨T3,hT3⟩ := eventually_atTop.1 ((ha.and hb).and (eventually_ge_atTop (0:ℝ)))
  have hc := lower_of_linear (fun t => X t 3) (fun t => field p (X t) 3) T3 Cc p.mu3 c0 hμ3
    (by dsimp [c0]; linarith [div_pos hCc hμ3])
    (fun t ht => hX.derivative t (hT3 t ht).2 3) (by
      intro t ht
      have hh := hT3 t ht
      have hx := hX.positive t hh.2
      have hab := mul_le_mul hh.1.1.le hh.1.2.le hb0.le (hx 1).le
      have hmult := mul_le_mul_of_nonneg_left hab (add_pos hγ1 hγ2).le
      have hs0 := (hx 0).le
      have ha1 := (hx 1).le
      have hb1 := (hx 2).le
      have hc1 := (hx 3).le
      have hrest : 0 ≤ X t 3*(p.eta1*X t 1+p.eta2*X t 2+p.alpha3*X t 0) := by positivity
      dsimp [Cc,field]
      nlinarith only [hmult,hrest])
  filter_upwards [hs,ha,hb,hc,hbox] with t hs' ha' hb' hc' hbox'
  intro i
  refine ⟨?_,populationBox_coordinate_le R (X t) hbox' i⟩
  have hmin0 : ε ≤ l := min_le_left _ _
  have hmin1 : ε ≤ a0 := (min_le_right _ _).trans (min_le_left _ _)
  have hmin2 : ε ≤ b0 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmin3 : ε ≤ c0 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  fin_cases i
  · exact hmin0.trans hs'.le
  · exact hmin1.trans ha'.le
  · exact hmin2.trans hb'.le
  · exact hmin3.trans hc'.le

/-- Positive global existence and an initial-state-independent species floor
for the literal source, at arbitrary strictly positive invading rates. -/
theorem source_strict_permanence (p : Rates) (hp : PositiveRates p)
    (he1 : p.mu1/p.alpha1 < p.recruitment/p.mu0)
    (he2 : p.mu2/p.alpha2 < p.recruitment/p.mu0) (hi : StrictMutualInvasion p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x0 : State, (∀ i, 0 < x0 i) →
      ∃ X : ℝ → State, X 0 = x0 ∧ IsTrajectory p X ∧
        ∀ᶠ t in atTop, ∀ i, ε ≤ X t i ∧ X t i ≤ p.recruitment/deathFloor p+1 := by
  obtain ⟨ε,hε,hfloor⟩ := general_trajectory_permanence p hp he1 he2 hi
  refine ⟨ε,hε,?_⟩
  intro x0 hx0
  obtain ⟨X,hX0,hX⟩ := general_positive_global p hp x0 hx0
  exact ⟨X,hX0,hX,hfloor X hX⟩

end OverlappingSiphonInvasion
