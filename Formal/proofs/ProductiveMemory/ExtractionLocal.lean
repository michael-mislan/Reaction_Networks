import proofs.FiniteCopy.LocalNonlinear
import proofs.ProductiveMemory.ExtractionEquilibria

namespace ProductiveMemory
open FiniteCopy Set
noncomputable section
set_option Elab.async false
def extractionLinear (A B z rho : ℝ) (y : Point) : Point :=
  sourceLinear A B z y - ![0,0,rho*y 2,0]

def lowExtractionPair (x v : Point) : ℝ :=
  (539561/500000 : ℝ)*x 0*v 0 + (-568413/1000000 : ℝ)*x 0*v 1 + (2227359/1000000 : ℝ)*x 0*v 2 + (326633/100000 : ℝ)*x 0*v 3 + (-568413/1000000 : ℝ)*x 1*v 0 + (211557/200000 : ℝ)*x 1*v 1 + (-548597/250000 : ℝ)*x 1*v 2 + (-80379/25000 : ℝ)*x 1*v 3 + (2227359/1000000 : ℝ)*x 2*v 0 + (-548597/250000 : ℝ)*x 2*v 1 + (398987/62500 : ℝ)*x 2*v 2 + (9601239/1000000 : ℝ)*x 2*v 3 + (326633/100000 : ℝ)*x 3*v 0 + (-80379/25000 : ℝ)*x 3*v 1 + (9601239/1000000 : ℝ)*x 3*v 2 + (7325563/500000 : ℝ)*x 3*v 3
def lowExtractionEnergy (x : Point) : ℝ := lowExtractionPair x x

theorem lowExtractionEnergy_lower (x : Point) : (1/200:ℝ)*normSq x ≤ lowExtractionEnergy x := by
  have hid : lowExtractionEnergy x-(1/200:ℝ)*normSq x = (537061/500000 : ℝ)*((1/1 : ℝ)*x 0 + (-568413/1074122 : ℝ)*x 1 + (2227359/1074122 : ℝ)*x 2 + (1633165/537061 : ℝ)*x 3)^2 + (807726191201/1074122000000 : ℝ)*((1/1 : ℝ)*x 1 + (-1090980616069/807726191201 : ℝ)*x 2 + (-1596849655230/807726191201 : ℝ)*x 3)^2 + (313507789190564431/807726191201000000 : ℝ)*((1/1 : ℝ)*x 2 + (662333669919277569/313507789190564431 : ℝ)*x 3)^2 + (2633473894677454066769/62701557838112886200000 : ℝ)*((1/1 : ℝ)*x 3)^2 := by
    unfold lowExtractionEnergy lowExtractionPair normSq
    ring
  have hp : 0 ≤ lowExtractionEnergy x-(1/200:ℝ)*normSq x := by
    rw [hid]
    positivity
  linarith only [hp]

theorem lowExtractionEnergy_upper (x : Point) : lowExtractionEnergy x ≤ 60*normSq x := by
  have hid : 60*normSq x-lowExtractionEnergy x = (29460439/500000 : ℝ)*((1/1 : ℝ)*x 0 + (568413/58920878 : ℝ)*x 1 + (-2227359/58920878 : ℝ)*x 2 + (-1633165/29460439 : ℝ)*x 3)^2 + (3472603965726201/58920878000000 : ℝ)*((1/1 : ℝ)*x 1 + (130561327443931/3472603965726201 : ℝ)*x 2 + (21255186060530/385844885080689 : ℝ)*x 3)^2 + (185606156211346843835569/3472603965726201000000 : ℝ)*((1/1 : ℝ)*x 2 + (-4884853145489925770367/26515165173049549119367 : ℝ)*x 3)^2 + (228957880200974417114424552967/5303033034609909823873400000 : ℝ)*((1/1 : ℝ)*x 3)^2 := by
    unfold lowExtractionEnergy lowExtractionPair normSq
    ring
  have hp : 0 ≤ 60*normSq x-lowExtractionEnergy x := by
    rw [hid]
    positivity
  linarith only [hp]

theorem low_extraction_linear (A B z rho : ℝ) (x : Point)
    (hA : A ∈ Icc (12/1 : ℝ) (14/1 : ℝ))
    (hB : B ∈ Icc (25153/1250 : ℝ) (201227/10000 : ℝ))
    (hz : z ∈ Icc (24543/25000 : ℝ) (49087/50000 : ℝ))
    (hrho : rho ∈ Icc (9999/1000000 : ℝ) (1/100 : ℝ))
    : 2*lowExtractionPair x (extractionLinear A B z rho x) ≤ -(84/100)*normSq x := by
  have e00 : |(-2726657/25000000000 : ℝ) * A + (351/250000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t00 := small_coefficient_product x 0 0 ((-2726657/25000000000 : ℝ) * A + (351/250000 : ℝ)) e00
  have e01 : |(2194611/50000000000 : ℝ) * A + (-36239/62500 : ℝ) * z + (56866326657/100000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t01 := small_coefficient_product x 0 1 ((2194611/50000000000 : ℝ) * A + (-36239/62500 : ℝ) * z + (56866326657/100000000000 : ℝ)) e01
  have e02 : |(-3324553/25000000000 : ℝ) * A + (-36239/62500 : ℝ) * B + (-297097/62500 : ℝ) * z + (-2227359/1000000 : ℝ) * rho + (8179111/500000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t02 := small_coefficient_product x 0 2 ((-3324553/25000000000 : ℝ) * A + (-36239/62500 : ℝ) * B + (-297097/62500 : ℝ) * z + (-2227359/1000000 : ℝ) * rho + (8179111/500000 : ℝ)) e02
  have e03 : |(-487391/2500000000 : ℝ) * A + (2509367/1000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t03 := small_coefficient_product x 0 3 ((-487391/2500000000 : ℝ) * A + (2509367/1000000000 : ℝ)) e03
  have e10 : |(2194611/50000000000 : ℝ) * A + (-36239/62500 : ℝ) * z + (56866326657/100000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t10 := small_coefficient_product x 1 0 ((2194611/50000000000 : ℝ) * A + (-36239/62500 : ℝ) * z + (56866326657/100000000000 : ℝ)) e10
  have e11 : |(56819/50000 : ℝ) * z + (-55780694611/50000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t11 := small_coefficient_product x 1 1 ((56819/50000 : ℝ) * z + (-55780694611/50000000000 : ℝ)) e11
  have e12 : |(56819/100000 : ℝ) * B + (2732419/1000000 : ℝ) * z + (548597/250000 : ℝ) * rho + (-706894875447/50000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t12 := small_coefficient_product x 1 2 ((56819/100000 : ℝ) * B + (2732419/1000000 : ℝ) * z + (548597/250000 : ℝ) * rho + (-706894875447/50000000000 : ℝ)) e12
  have e13 : |(-3119749/1000000 : ℝ) * z + (15313674971/5000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t13 := small_coefficient_product x 1 3 ((-3119749/1000000 : ℝ) * z + (15313674971/5000000000 : ℝ)) e13
  have e20 : |(-3324553/25000000000 : ℝ) * A + (-36239/62500 : ℝ) * B + (-297097/62500 : ℝ) * z + (-2227359/1000000 : ℝ) * rho + (8179111/500000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t20 := small_coefficient_product x 2 0 ((-3324553/25000000000 : ℝ) * A + (-36239/62500 : ℝ) * B + (-297097/62500 : ℝ) * z + (-2227359/1000000 : ℝ) * rho + (8179111/500000 : ℝ)) e20
  have e21 : |(56819/100000 : ℝ) * B + (2732419/1000000 : ℝ) * z + (548597/250000 : ℝ) * rho + (-706894875447/50000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t21 := small_coefficient_product x 2 1 ((56819/100000 : ℝ) * B + (2732419/1000000 : ℝ) * z + (548597/250000 : ℝ) * rho + (-706894875447/50000000000 : ℝ)) e21
  have e22 : |(-392409/100000 : ℝ) * B + (-633269/25000 : ℝ) * z + (-398987/31250 : ℝ) * rho + (3248697/31250 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t22 := small_coefficient_product x 2 2 ((-392409/100000 : ℝ) * B + (-633269/25000 : ℝ) * z + (-398987/31250 : ℝ) * rho + (3248697/31250 : ℝ)) e22
  have e23 : |(-3119749/1000000 : ℝ) * B + (-568919/31250 : ℝ) * z + (-9601239/1000000 : ℝ) * rho + (807461298761/10000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t23 := small_coefficient_product x 2 3 ((-3119749/1000000 : ℝ) * B + (-568919/31250 : ℝ) * z + (-9601239/1000000 : ℝ) * rho + (807461298761/10000000000 : ℝ)) e23
  have e30 : |(-487391/2500000000 : ℝ) * A + (2509367/1000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t30 := small_coefficient_product x 3 0 ((-487391/2500000000 : ℝ) * A + (2509367/1000000000 : ℝ)) e30
  have e31 : |(-3119749/1000000 : ℝ) * z + (15313674971/5000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t31 := small_coefficient_product x 3 1 ((-3119749/1000000 : ℝ) * z + (15313674971/5000000000 : ℝ)) e31
  have e32 : |(-3119749/1000000 : ℝ) * B + (-568919/31250 : ℝ) * z + (-9601239/1000000 : ℝ) * rho + (807461298761/10000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t32 := small_coefficient_product x 3 2 ((-3119749/1000000 : ℝ) * B + (-568919/31250 : ℝ) * z + (-9601239/1000000 : ℝ) * rho + (807461298761/10000000000 : ℝ)) e32
  have e33 : |(-563/2500000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t33 := small_coefficient_product x 3 3 ((-563/2500000000 : ℝ)) e33
  have hid : 2*lowExtractionPair x (extractionLinear A B z rho x) = -normSq x + (((-2726657/25000000000 : ℝ) * A + (351/250000 : ℝ))*x 0*x 0 + ((2194611/50000000000 : ℝ) * A + (-36239/62500 : ℝ) * z + (56866326657/100000000000 : ℝ))*x 0*x 1 + ((-3324553/25000000000 : ℝ) * A + (-36239/62500 : ℝ) * B + (-297097/62500 : ℝ) * z + (-2227359/1000000 : ℝ) * rho + (8179111/500000 : ℝ))*x 0*x 2 + ((-487391/2500000000 : ℝ) * A + (2509367/1000000000 : ℝ))*x 0*x 3 + ((2194611/50000000000 : ℝ) * A + (-36239/62500 : ℝ) * z + (56866326657/100000000000 : ℝ))*x 1*x 0 + ((56819/50000 : ℝ) * z + (-55780694611/50000000000 : ℝ))*x 1*x 1 + ((56819/100000 : ℝ) * B + (2732419/1000000 : ℝ) * z + (548597/250000 : ℝ) * rho + (-706894875447/50000000000 : ℝ))*x 1*x 2 + ((-3119749/1000000 : ℝ) * z + (15313674971/5000000000 : ℝ))*x 1*x 3 + ((-3324553/25000000000 : ℝ) * A + (-36239/62500 : ℝ) * B + (-297097/62500 : ℝ) * z + (-2227359/1000000 : ℝ) * rho + (8179111/500000 : ℝ))*x 2*x 0 + ((56819/100000 : ℝ) * B + (2732419/1000000 : ℝ) * z + (548597/250000 : ℝ) * rho + (-706894875447/50000000000 : ℝ))*x 2*x 1 + ((-392409/100000 : ℝ) * B + (-633269/25000 : ℝ) * z + (-398987/31250 : ℝ) * rho + (3248697/31250 : ℝ))*x 2*x 2 + ((-3119749/1000000 : ℝ) * B + (-568919/31250 : ℝ) * z + (-9601239/1000000 : ℝ) * rho + (807461298761/10000000000 : ℝ))*x 2*x 3 + ((-487391/2500000000 : ℝ) * A + (2509367/1000000000 : ℝ))*x 3*x 0 + ((-3119749/1000000 : ℝ) * z + (15313674971/5000000000 : ℝ))*x 3*x 1 + ((-3119749/1000000 : ℝ) * B + (-568919/31250 : ℝ) * z + (-9601239/1000000 : ℝ) * rho + (807461298761/10000000000 : ℝ))*x 3*x 2 + ((-563/2500000000 : ℝ))*x 3*x 3) := by
    norm_num [lowExtractionPair,extractionLinear,sourceLinear,normSq,Matrix.cons_val_two,Matrix.cons_val_three]
    ring
  rw [hid]
  linarith only [t00,t01,t02,t03,t10,t11,t12,t13,t20,t21,t22,t23,t30,t31,t32,t33]

theorem low_extraction_cubic (x : Point) (hx : ∀ i, |x i| ≤ 1/400) :
    2*lowExtractionPair x (sourceRemainder x) ≤ (1/4)*normSq x := by
  have t0 := cubic_term_bound x 0 0 0 (-2726657/50000000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t0
  have t1 := cubic_term_bound x 0 0 1 (2194611/50000000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t1
  have t2 := cubic_term_bound x 0 0 2 (-3324553/25000000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t2
  have t3 := cubic_term_bound x 0 0 3 (-487391/2500000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t3
  have t4 := cubic_term_bound x 0 1 2 (-36239/31250 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t4
  have t5 := cubic_term_bound x 0 2 2 (-297097/62500 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t5
  have t6 := cubic_term_bound x 1 1 2 (56819/50000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t6
  have t7 := cubic_term_bound x 1 2 2 (385187/500000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t7
  have t8 := cubic_term_bound x 1 2 3 (-3119749/500000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t8
  have t9 := cubic_term_bound x 2 2 2 (-633269/50000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t9
  have t10 := cubic_term_bound x 2 2 3 (-568919/31250 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t10
  have hid : 2*lowExtractionPair x (sourceRemainder x) = (-2726657/50000000000 : ℝ)*x 0*x 0*x 0 + (2194611/50000000000 : ℝ)*x 0*x 0*x 1 + (-3324553/25000000000 : ℝ)*x 0*x 0*x 2 + (-487391/2500000000 : ℝ)*x 0*x 0*x 3 + (-36239/31250 : ℝ)*x 0*x 1*x 2 + (-297097/62500 : ℝ)*x 0*x 2*x 2 + (56819/50000 : ℝ)*x 1*x 1*x 2 + (385187/500000 : ℝ)*x 1*x 2*x 2 + (-3119749/500000 : ℝ)*x 1*x 2*x 3 + (-633269/50000 : ℝ)*x 2*x 2*x 2 + (-568919/31250 : ℝ)*x 2*x 2*x 3 := by
    norm_num [lowExtractionPair,sourceRemainder,Matrix.cons_val_two,Matrix.cons_val_three]
    ring
  rw [hid]
  nlinarith only [normSq_nonneg x,t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10]

def highExtractionPair (x v : Point) : ℝ :=
  (244049/250000 : ℝ)*x 0*v 0 + (-93801/62500 : ℝ)*x 0*v 1 + (2954639/1000000 : ℝ)*x 0*v 2 + (2205629/500000 : ℝ)*x 0*v 3 + (-93801/62500 : ℝ)*x 1*v 0 + (5195401/1000000 : ℝ)*x 1*v 1 + (-2080217/250000 : ℝ)*x 1*v 2 + (-6269591/500000 : ℝ)*x 1*v 3 + (2954639/1000000 : ℝ)*x 2*v 0 + (-2080217/250000 : ℝ)*x 2*v 1 + (14137961/1000000 : ℝ)*x 2*v 2 + (10664797/500000 : ℝ)*x 2*v 3 + (2205629/500000 : ℝ)*x 3*v 0 + (-6269591/500000 : ℝ)*x 3*v 1 + (10664797/500000 : ℝ)*x 3*v 2 + (32242779/1000000 : ℝ)*x 3*v 3
def highExtractionEnergy (x : Point) : ℝ := highExtractionPair x x

theorem highExtractionEnergy_lower (x : Point) : (1/200:ℝ)*normSq x ≤ highExtractionEnergy x := by
  have hid : highExtractionEnergy x-(1/200:ℝ)*normSq x = (242799/250000 : ℝ)*((1/1 : ℝ)*x 0 + (-125068/80933 : ℝ)*x 1 + (2954639/971196 : ℝ)*x 2 + (2205629/485598 : ℝ)*x 3)^2 + (46474133729/16186600000 : ℝ)*((1/1 : ℝ)*x 1 + (-303902019392/232370668645 : ℝ)*x 2 + (-463126401262/232370668645 : ℝ)*x 3)^2 + (650449065948516379/2788448023740000000 : ℝ)*((1/1 : ℝ)*x 2 + (1186467073991769074/650449065948516379 : ℝ)*x 3)^2 + (13273467198080330569049/650449065948516379000000 : ℝ)*((1/1 : ℝ)*x 3)^2 := by
    unfold highExtractionEnergy highExtractionPair normSq
    ring
  have hp : 0 ≤ highExtractionEnergy x-(1/200:ℝ)*normSq x := by
    rw [hid]
    positivity
  linarith only [hp]

theorem highExtractionEnergy_upper (x : Point) : highExtractionEnergy x ≤ 60*normSq x := by
  have hid : 60*normSq x-highExtractionEnergy x = (14755951/250000 : ℝ)*((1/1 : ℝ)*x 0 + (375204/14755951 : ℝ)*x 1 + (-2954639/59023804 : ℝ)*x 2 + (-2205629/29511902 : ℝ)*x 3)^2 + (161626173050437/2951190200000 : ℝ)*((1/1 : ℝ)*x 1 + (123890912856824/808130865252185 : ℝ)*x 2 + (186682676818714/808130865252185 : ℝ)*x 3)^2 + (143611261295356677923621/3232523461008740000000 : ℝ)*((1/1 : ℝ)*x 2 + (-75931769359413170669074/143611261295356677923621 : ℝ)*x 3)^2 + (1735562416502464972244355744049/143611261295356677923621000000 : ℝ)*((1/1 : ℝ)*x 3)^2 := by
    unfold highExtractionEnergy highExtractionPair normSq
    ring
  have hp : 0 ≤ 60*normSq x-highExtractionEnergy x := by
    rw [hid]
    positivity
  linarith only [hp]

theorem high_extraction_linear (A B z rho : ℝ) (x : Point)
    (hA : A ∈ Icc (20/1 : ℝ) (22/1 : ℝ))
    (hB : B ∈ Icc (61347/5000 : ℝ) (122697/10000 : ℝ))
    (hz : z ∈ Icc (144507/50000 : ℝ) (289017/100000 : ℝ))
    (hrho : rho ∈ Icc (9999/1000000 : ℝ) (1/100 : ℝ))
    : 2*highExtractionPair x (extractionLinear A B z rho x) ≤ -(84/100)*normSq x := by
  have e00 : |(-431651/3125000000 : ℝ) * A + (1431/500000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t00 := small_coefficient_product x 0 0 ((-431651/3125000000 : ℝ) * A + (1431/500000 : ℝ)) e00
  have e01 : |(8197033/50000000000 : ℝ) * A + (-477627/1000000 : ℝ) * z + (17212694151/12500000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t01 := small_coefficient_product x 0 1 ((8197033/50000000000 : ℝ) * A + (-477627/1000000 : ℝ) * z + (17212694151/12500000000 : ℝ)) e01
  have e02 : |(-7115073/25000000000 : ℝ) * A + (-477627/1000000 : ℝ) * B + (-74901/12500 : ℝ) * z + (-2954639/1000000 : ℝ) * rho + (23213719/1000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t02 := small_coefficient_product x 0 2 ((-7115073/25000000000 : ℝ) * A + (-477627/1000000 : ℝ) * B + (-74901/12500 : ℝ) * z + (-2954639/1000000 : ℝ) * rho + (23213719/1000000 : ℝ)) e02
  have e03 : |(-10680849/25000000000 : ℝ) * A + (44279371/5000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t03 := small_coefficient_product x 0 3 ((-10680849/25000000000 : ℝ) * A + (44279371/5000000000 : ℝ)) e03
  have e10 : |(8197033/50000000000 : ℝ) * A + (-477627/1000000 : ℝ) * z + (17212694151/12500000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t10 := small_coefficient_product x 1 0 ((8197033/50000000000 : ℝ) * A + (-477627/1000000 : ℝ) * z + (17212694151/12500000000 : ℝ)) e10
  have e11 : |(1624651/500000 : ℝ) * z + (-469548297033/50000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t11 := small_coefficient_product x 1 1 ((1624651/500000 : ℝ) * z + (-469548297033/50000000000 : ℝ)) e11
  have e12 : |(1624651/1000000 : ℝ) * B + (6773881/500000 : ℝ) * z + (2080217/250000 : ℝ) * rho + (-2958600684927/50000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t12 := small_coefficient_product x 1 2 ((1624651/1000000 : ℝ) * B + (6773881/500000 : ℝ) * z + (2080217/250000 : ℝ) * rho + (-2958600684927/50000000000 : ℝ)) e12
  have e13 : |(-2189577/500000 : ℝ) * z + (632820476759/50000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t13 := small_coefficient_product x 1 3 ((-2189577/500000 : ℝ) * z + (632820476759/50000000000 : ℝ)) e13
  have e20 : |(-7115073/25000000000 : ℝ) * A + (-477627/1000000 : ℝ) * B + (-74901/12500 : ℝ) * z + (-2954639/1000000 : ℝ) * rho + (23213719/1000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t20 := small_coefficient_product x 2 0 ((-7115073/25000000000 : ℝ) * A + (-477627/1000000 : ℝ) * B + (-74901/12500 : ℝ) * z + (-2954639/1000000 : ℝ) * rho + (23213719/1000000 : ℝ)) e20
  have e21 : |(1624651/1000000 : ℝ) * B + (6773881/500000 : ℝ) * z + (2080217/250000 : ℝ) * rho + (-2958600684927/50000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t21 := small_coefficient_product x 2 1 ((1624651/1000000 : ℝ) * B + (6773881/500000 : ℝ) * z + (2080217/250000 : ℝ) * rho + (-2958600684927/50000000000 : ℝ)) e21
  have e22 : |(-1431227/250000 : ℝ) * B + (-868291/15625 : ℝ) * z + (-14137961/500000 : ℝ) * rho + (7222883/31250 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t22 := small_coefficient_product x 2 2 ((-1431227/250000 : ℝ) * B + (-868291/15625 : ℝ) * z + (-14137961/500000 : ℝ) * rho + (7222883/31250 : ℝ)) e22
  have e23 : |(-2189577/500000 : ℝ) * B + (-10416409/250000 : ℝ) * z + (-10664797/500000 : ℝ) * rho + (871817610203/5000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t23 := small_coefficient_product x 2 3 ((-2189577/500000 : ℝ) * B + (-10416409/250000 : ℝ) * z + (-10664797/500000 : ℝ) * rho + (871817610203/5000000000 : ℝ)) e23
  have e30 : |(-10680849/25000000000 : ℝ) * A + (44279371/5000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t30 := small_coefficient_product x 3 0 ((-10680849/25000000000 : ℝ) * A + (44279371/5000000000 : ℝ)) e30
  have e31 : |(-2189577/500000 : ℝ) * z + (632820476759/50000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t31 := small_coefficient_product x 3 1 ((-2189577/500000 : ℝ) * z + (632820476759/50000000000 : ℝ)) e31
  have e32 : |(-2189577/500000 : ℝ) * B + (-10416409/250000 : ℝ) * z + (-10664797/500000 : ℝ) * rho + (871817610203/5000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t32 := small_coefficient_product x 3 2 ((-2189577/500000 : ℝ) * B + (-10416409/250000 : ℝ) * z + (-10664797/500000 : ℝ) * rho + (871817610203/5000000000 : ℝ)) e32
  have e33 : |(-2779/5000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2,hrho.1,hrho.2]
  have t33 := small_coefficient_product x 3 3 ((-2779/5000000000 : ℝ)) e33
  have hid : 2*highExtractionPair x (extractionLinear A B z rho x) = -normSq x + (((-431651/3125000000 : ℝ) * A + (1431/500000 : ℝ))*x 0*x 0 + ((8197033/50000000000 : ℝ) * A + (-477627/1000000 : ℝ) * z + (17212694151/12500000000 : ℝ))*x 0*x 1 + ((-7115073/25000000000 : ℝ) * A + (-477627/1000000 : ℝ) * B + (-74901/12500 : ℝ) * z + (-2954639/1000000 : ℝ) * rho + (23213719/1000000 : ℝ))*x 0*x 2 + ((-10680849/25000000000 : ℝ) * A + (44279371/5000000000 : ℝ))*x 0*x 3 + ((8197033/50000000000 : ℝ) * A + (-477627/1000000 : ℝ) * z + (17212694151/12500000000 : ℝ))*x 1*x 0 + ((1624651/500000 : ℝ) * z + (-469548297033/50000000000 : ℝ))*x 1*x 1 + ((1624651/1000000 : ℝ) * B + (6773881/500000 : ℝ) * z + (2080217/250000 : ℝ) * rho + (-2958600684927/50000000000 : ℝ))*x 1*x 2 + ((-2189577/500000 : ℝ) * z + (632820476759/50000000000 : ℝ))*x 1*x 3 + ((-7115073/25000000000 : ℝ) * A + (-477627/1000000 : ℝ) * B + (-74901/12500 : ℝ) * z + (-2954639/1000000 : ℝ) * rho + (23213719/1000000 : ℝ))*x 2*x 0 + ((1624651/1000000 : ℝ) * B + (6773881/500000 : ℝ) * z + (2080217/250000 : ℝ) * rho + (-2958600684927/50000000000 : ℝ))*x 2*x 1 + ((-1431227/250000 : ℝ) * B + (-868291/15625 : ℝ) * z + (-14137961/500000 : ℝ) * rho + (7222883/31250 : ℝ))*x 2*x 2 + ((-2189577/500000 : ℝ) * B + (-10416409/250000 : ℝ) * z + (-10664797/500000 : ℝ) * rho + (871817610203/5000000000 : ℝ))*x 2*x 3 + ((-10680849/25000000000 : ℝ) * A + (44279371/5000000000 : ℝ))*x 3*x 0 + ((-2189577/500000 : ℝ) * z + (632820476759/50000000000 : ℝ))*x 3*x 1 + ((-2189577/500000 : ℝ) * B + (-10416409/250000 : ℝ) * z + (-10664797/500000 : ℝ) * rho + (871817610203/5000000000 : ℝ))*x 3*x 2 + ((-2779/5000000000 : ℝ))*x 3*x 3) := by
    norm_num [highExtractionPair,extractionLinear,sourceLinear,normSq,Matrix.cons_val_two,Matrix.cons_val_three]
    ring
  rw [hid]
  linarith only [t00,t01,t02,t03,t10,t11,t12,t13,t20,t21,t22,t23,t30,t31,t32,t33]

theorem high_extraction_cubic (x : Point) (hx : ∀ i, |x i| ≤ 1/400) :
    2*highExtractionPair x (sourceRemainder x) ≤ (1/4)*normSq x := by
  have t0 := cubic_term_bound x 0 0 0 (-431651/6250000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t0
  have t1 := cubic_term_bound x 0 0 1 (8197033/50000000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t1
  have t2 := cubic_term_bound x 0 0 2 (-7115073/25000000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t2
  have t3 := cubic_term_bound x 0 0 3 (-10680849/25000000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t3
  have t4 := cubic_term_bound x 0 1 2 (-477627/500000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t4
  have t5 := cubic_term_bound x 0 2 2 (-74901/12500 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t5
  have t6 := cubic_term_bound x 1 1 2 (1624651/500000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t6
  have t7 := cubic_term_bound x 1 2 2 (2671327/250000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t7
  have t8 := cubic_term_bound x 1 2 3 (-2189577/250000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t8
  have t9 := cubic_term_bound x 2 2 2 (-868291/31250 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t9
  have t10 := cubic_term_bound x 2 2 3 (-10416409/250000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t10
  have hid : 2*highExtractionPair x (sourceRemainder x) = (-431651/6250000000 : ℝ)*x 0*x 0*x 0 + (8197033/50000000000 : ℝ)*x 0*x 0*x 1 + (-7115073/25000000000 : ℝ)*x 0*x 0*x 2 + (-10680849/25000000000 : ℝ)*x 0*x 0*x 3 + (-477627/500000 : ℝ)*x 0*x 1*x 2 + (-74901/12500 : ℝ)*x 0*x 2*x 2 + (1624651/500000 : ℝ)*x 1*x 1*x 2 + (2671327/250000 : ℝ)*x 1*x 2*x 2 + (-2189577/250000 : ℝ)*x 1*x 2*x 3 + (-868291/31250 : ℝ)*x 2*x 2*x 2 + (-10416409/250000 : ℝ)*x 2*x 2*x 3 := by
    norm_num [highExtractionPair,sourceRemainder,Matrix.cons_val_two,Matrix.cons_val_three]
    ring
  rw [hid]
  nlinarith only [normSq_nonneg x,t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10]

end
end ProductiveMemory
