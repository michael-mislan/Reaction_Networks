import proofs.ProductiveMemory.ExtractionLocal
import proofs.HeritableCompositions.GrowthEnergy

namespace ProductiveMemory
open FiniteCopy HeritableCompositions
noncomputable section
set_option Elab.async false

theorem low_extraction_pair_box (y v : Point) (r : ℝ) (hr : 0 ≤ r)
    (hy : ∀ i, |y i| ≤ r) (hv : ∀ i, |v i| ≤ 36) :
    |lowExtractionPair y v| ≤ 5600*r := by
  apply abs_le.mpr
  constructor
  · have t0 := bilinear_term_bound (-539561/500000:ℝ) (y 0) (v 0) r hr (hy 0) (hv 0)
    have t1 := bilinear_term_bound (568413/1000000:ℝ) (y 0) (v 1) r hr (hy 0) (hv 1)
    have t2 := bilinear_term_bound (-2227359/1000000:ℝ) (y 0) (v 2) r hr (hy 0) (hv 2)
    have t3 := bilinear_term_bound (-326633/100000:ℝ) (y 0) (v 3) r hr (hy 0) (hv 3)
    have t4 := bilinear_term_bound (568413/1000000:ℝ) (y 1) (v 0) r hr (hy 1) (hv 0)
    have t5 := bilinear_term_bound (-211557/200000:ℝ) (y 1) (v 1) r hr (hy 1) (hv 1)
    have t6 := bilinear_term_bound (548597/250000:ℝ) (y 1) (v 2) r hr (hy 1) (hv 2)
    have t7 := bilinear_term_bound (80379/25000:ℝ) (y 1) (v 3) r hr (hy 1) (hv 3)
    have t8 := bilinear_term_bound (-2227359/1000000:ℝ) (y 2) (v 0) r hr (hy 2) (hv 0)
    have t9 := bilinear_term_bound (548597/250000:ℝ) (y 2) (v 1) r hr (hy 2) (hv 1)
    have t10 := bilinear_term_bound (-398987/62500:ℝ) (y 2) (v 2) r hr (hy 2) (hv 2)
    have t11 := bilinear_term_bound (-9601239/1000000:ℝ) (y 2) (v 3) r hr (hy 2) (hv 3)
    have t12 := bilinear_term_bound (-326633/100000:ℝ) (y 3) (v 0) r hr (hy 3) (hv 0)
    have t13 := bilinear_term_bound (80379/25000:ℝ) (y 3) (v 1) r hr (hy 3) (hv 1)
    have t14 := bilinear_term_bound (-9601239/1000000:ℝ) (y 3) (v 2) r hr (hy 3) (hv 2)
    have t15 := bilinear_term_bound (-7325563/500000:ℝ) (y 3) (v 3) r hr (hy 3) (hv 3)
    norm_num only [abs_of_pos,abs_of_neg] at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    unfold lowExtractionPair
    linarith only [hr,t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15]
  · have t0 := bilinear_term_bound (539561/500000:ℝ) (y 0) (v 0) r hr (hy 0) (hv 0)
    have t1 := bilinear_term_bound (-568413/1000000:ℝ) (y 0) (v 1) r hr (hy 0) (hv 1)
    have t2 := bilinear_term_bound (2227359/1000000:ℝ) (y 0) (v 2) r hr (hy 0) (hv 2)
    have t3 := bilinear_term_bound (326633/100000:ℝ) (y 0) (v 3) r hr (hy 0) (hv 3)
    have t4 := bilinear_term_bound (-568413/1000000:ℝ) (y 1) (v 0) r hr (hy 1) (hv 0)
    have t5 := bilinear_term_bound (211557/200000:ℝ) (y 1) (v 1) r hr (hy 1) (hv 1)
    have t6 := bilinear_term_bound (-548597/250000:ℝ) (y 1) (v 2) r hr (hy 1) (hv 2)
    have t7 := bilinear_term_bound (-80379/25000:ℝ) (y 1) (v 3) r hr (hy 1) (hv 3)
    have t8 := bilinear_term_bound (2227359/1000000:ℝ) (y 2) (v 0) r hr (hy 2) (hv 0)
    have t9 := bilinear_term_bound (-548597/250000:ℝ) (y 2) (v 1) r hr (hy 2) (hv 1)
    have t10 := bilinear_term_bound (398987/62500:ℝ) (y 2) (v 2) r hr (hy 2) (hv 2)
    have t11 := bilinear_term_bound (9601239/1000000:ℝ) (y 2) (v 3) r hr (hy 2) (hv 3)
    have t12 := bilinear_term_bound (326633/100000:ℝ) (y 3) (v 0) r hr (hy 3) (hv 0)
    have t13 := bilinear_term_bound (-80379/25000:ℝ) (y 3) (v 1) r hr (hy 3) (hv 1)
    have t14 := bilinear_term_bound (9601239/1000000:ℝ) (y 3) (v 2) r hr (hy 3) (hv 2)
    have t15 := bilinear_term_bound (7325563/500000:ℝ) (y 3) (v 3) r hr (hy 3) (hv 3)
    norm_num only [abs_of_pos,abs_of_neg] at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    unfold lowExtractionPair
    linarith only [hr,t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15]

theorem low_extraction_energy_sub (y v : Point) (q : ℝ) :
    lowExtractionEnergy (fun i => y i-q*v i) = lowExtractionEnergy y-2*q*lowExtractionPair y v+q^2*lowExtractionEnergy v := by
  unfold lowExtractionEnergy lowExtractionPair
  ring

theorem low_extraction_membrane_energy (v : Point) (hv : ∀ i, |v i| ≤ 36) :
    lowExtractionEnergy v ≤ 211722 := by
  have h := low_extraction_pair_box v v 36 (by norm_num) hv hv
  change lowExtractionPair v v ≤ _
  linarith [le_abs_self (lowExtractionPair v v)]

theorem high_extraction_pair_box (y v : Point) (r : ℝ) (hr : 0 ≤ r)
    (hy : ∀ i, |y i| ≤ r) (hv : ∀ i, |v i| ≤ 36) :
    |highExtractionPair y v| ≤ 5600*r := by
  apply abs_le.mpr
  constructor
  · have t0 := bilinear_term_bound (-244049/250000:ℝ) (y 0) (v 0) r hr (hy 0) (hv 0)
    have t1 := bilinear_term_bound (93801/62500:ℝ) (y 0) (v 1) r hr (hy 0) (hv 1)
    have t2 := bilinear_term_bound (-2954639/1000000:ℝ) (y 0) (v 2) r hr (hy 0) (hv 2)
    have t3 := bilinear_term_bound (-2205629/500000:ℝ) (y 0) (v 3) r hr (hy 0) (hv 3)
    have t4 := bilinear_term_bound (93801/62500:ℝ) (y 1) (v 0) r hr (hy 1) (hv 0)
    have t5 := bilinear_term_bound (-5195401/1000000:ℝ) (y 1) (v 1) r hr (hy 1) (hv 1)
    have t6 := bilinear_term_bound (2080217/250000:ℝ) (y 1) (v 2) r hr (hy 1) (hv 2)
    have t7 := bilinear_term_bound (6269591/500000:ℝ) (y 1) (v 3) r hr (hy 1) (hv 3)
    have t8 := bilinear_term_bound (-2954639/1000000:ℝ) (y 2) (v 0) r hr (hy 2) (hv 0)
    have t9 := bilinear_term_bound (2080217/250000:ℝ) (y 2) (v 1) r hr (hy 2) (hv 1)
    have t10 := bilinear_term_bound (-14137961/1000000:ℝ) (y 2) (v 2) r hr (hy 2) (hv 2)
    have t11 := bilinear_term_bound (-10664797/500000:ℝ) (y 2) (v 3) r hr (hy 2) (hv 3)
    have t12 := bilinear_term_bound (-2205629/500000:ℝ) (y 3) (v 0) r hr (hy 3) (hv 0)
    have t13 := bilinear_term_bound (6269591/500000:ℝ) (y 3) (v 1) r hr (hy 3) (hv 1)
    have t14 := bilinear_term_bound (-10664797/500000:ℝ) (y 3) (v 2) r hr (hy 3) (hv 2)
    have t15 := bilinear_term_bound (-32242779/1000000:ℝ) (y 3) (v 3) r hr (hy 3) (hv 3)
    norm_num only [abs_of_pos,abs_of_neg] at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    unfold highExtractionPair
    linarith only [hr,t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15]
  · have t0 := bilinear_term_bound (244049/250000:ℝ) (y 0) (v 0) r hr (hy 0) (hv 0)
    have t1 := bilinear_term_bound (-93801/62500:ℝ) (y 0) (v 1) r hr (hy 0) (hv 1)
    have t2 := bilinear_term_bound (2954639/1000000:ℝ) (y 0) (v 2) r hr (hy 0) (hv 2)
    have t3 := bilinear_term_bound (2205629/500000:ℝ) (y 0) (v 3) r hr (hy 0) (hv 3)
    have t4 := bilinear_term_bound (-93801/62500:ℝ) (y 1) (v 0) r hr (hy 1) (hv 0)
    have t5 := bilinear_term_bound (5195401/1000000:ℝ) (y 1) (v 1) r hr (hy 1) (hv 1)
    have t6 := bilinear_term_bound (-2080217/250000:ℝ) (y 1) (v 2) r hr (hy 1) (hv 2)
    have t7 := bilinear_term_bound (-6269591/500000:ℝ) (y 1) (v 3) r hr (hy 1) (hv 3)
    have t8 := bilinear_term_bound (2954639/1000000:ℝ) (y 2) (v 0) r hr (hy 2) (hv 0)
    have t9 := bilinear_term_bound (-2080217/250000:ℝ) (y 2) (v 1) r hr (hy 2) (hv 1)
    have t10 := bilinear_term_bound (14137961/1000000:ℝ) (y 2) (v 2) r hr (hy 2) (hv 2)
    have t11 := bilinear_term_bound (10664797/500000:ℝ) (y 2) (v 3) r hr (hy 2) (hv 3)
    have t12 := bilinear_term_bound (2205629/500000:ℝ) (y 3) (v 0) r hr (hy 3) (hv 0)
    have t13 := bilinear_term_bound (-6269591/500000:ℝ) (y 3) (v 1) r hr (hy 3) (hv 1)
    have t14 := bilinear_term_bound (10664797/500000:ℝ) (y 3) (v 2) r hr (hy 3) (hv 2)
    have t15 := bilinear_term_bound (32242779/1000000:ℝ) (y 3) (v 3) r hr (hy 3) (hv 3)
    norm_num only [abs_of_pos,abs_of_neg] at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    unfold highExtractionPair
    linarith only [hr,t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15]

theorem high_extraction_energy_sub (y v : Point) (q : ℝ) :
    highExtractionEnergy (fun i => y i-q*v i) = highExtractionEnergy y-2*q*highExtractionPair y v+q^2*highExtractionEnergy v := by
  unfold highExtractionEnergy highExtractionPair
  ring

theorem high_extraction_membrane_energy (v : Point) (hv : ∀ i, |v i| ≤ 36) :
    highExtractionEnergy v ≤ 211722 := by
  have h := high_extraction_pair_box v v 36 (by norm_num) hv hv
  change highExtractionPair v v ≤ _
  linarith [le_abs_self (highExtractionPair v v)]

end
end ProductiveMemory
