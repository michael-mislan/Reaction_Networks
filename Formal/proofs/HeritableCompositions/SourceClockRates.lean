import proofs.HeritableCompositions.GrowthWellBounds
import proofs.HeritableCompositions.MembraneClock

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

theorem membrane_rate_identity (γ : ℝ) (c : Compartment) (hm : 0 < c.2) :
    γ*(c.1 2 : ℝ) = γ*(c.2 : ℝ)*concentration c.2 c.1 2 := by
  have hm0 : (c.2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  unfold concentration
  field_simp

theorem growth_domain_membrane_rates (γ l u : ℝ) (hγ : 0 ≤ γ) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (N : ℕ) (hN : 1 ≤ N) (s : Point) (hs : ∀ i, s i ≤ 34)
    (E : Point → ℝ) (hE : ∀ y, (1/200)*normSq y ≤ E y)
    (hsl : l+1/400 ≤ s 2) (hsu : s 2 ≤ u-1/400)
    (b : ℝ) (hb : b ≤ 1/32000000) (c : Compartment) (hc : c ∈ growthDomain N s E b) :
    (γ*l)*(N : ℝ) ≤ γ*(c.1 2 : ℝ) ∧ γ*(c.1 2 : ℝ) ≤ 2*(γ*u)*(N : ℝ) := by
  have hm := (mem_growthDomain N hN c s hs E hE b hb).mp hc
  have hy := abs_le.mp (small_energy_coordinates E hE _ (hm.2.2.trans_le hb) 2)
  have hz : l ≤ concentration c.2 c.1 2 ∧ concentration c.2 c.1 2 ≤ u := by
    constructor <;> linarith only [hy.1,hy.2,hsl,hsu]
  have hNm : (N : ℝ) ≤ c.2 := by exact_mod_cast hm.1
  have hmN : (c.2 : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hm.2.1
  rw [membrane_rate_identity γ c (by omega)]
  have hlo := mul_le_mul_of_nonneg_left hNm (mul_nonneg hγ hl)
  have hhi := mul_le_mul_of_nonneg_left hmN (mul_nonneg hγ hu)
  have hzl := mul_le_mul_of_nonneg_left hz.1 (by positivity : 0 ≤ γ*(c.2 : ℝ))
  have hzu := mul_le_mul_of_nonneg_left hz.2 (by positivity : 0 ≤ γ*(c.2 : ℝ))
  constructor <;> nlinarith only [hlo,hhi,hzl,hzu]

theorem low_domain_membrane_rates (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hγ : 0 ≤ γ) (N : ℕ) (hN : 1 ≤ N) (b : ℝ) (hb : b ≤ 1/32000000)
    (c : Compartment) (hc : c ∈ growthDomain N (pointOfState (lift sourceRates z)) lowEnergy b) :
    (γ*(99/100))*(N : ℝ) ≤ γ*(c.1 2 : ℝ) ∧
      γ*(c.1 2 : ℝ) ≤ 2*(γ*(101/100))*(N : ℝ) := by
  apply growth_domain_membrane_rates γ (99/100) (101/100) hγ (by norm_num) (by norm_num)
    N hN _ (lowroot_upper z hz) lowEnergy lowEnergy_lower _ _ b hb c hc
  · change 99/100+1/400 ≤ z
    linarith only [hz.1]
  · change z ≤ 101/100-1/400
    linarith only [hz.2]

theorem high_domain_membrane_rates (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hγ : 0 ≤ γ) (N : ℕ) (hN : 1 ≤ N) (b : ℝ) (hb : b ≤ 1/32000000)
    (c : Compartment) (hc : c ∈ growthDomain N (pointOfState (lift sourceRates z)) highEnergy b) :
    (γ*(297/100))*(N : ℝ) ≤ γ*(c.1 2 : ℝ) ∧
      γ*(c.1 2 : ℝ) ≤ 2*(γ*3)*(N : ℝ) := by
  apply growth_domain_membrane_rates γ (297/100) 3 hγ (by norm_num) (by norm_num)
    N hN _ (highroot_upper z hz) highEnergy highEnergy_lower _ _ b hb c hc
  · change 297/100+1/400 ≤ z
    linarith only [hz.1]
  · change z ≤ 3-1/400
    linarith only [hz.2]

end HeritableCompositions
