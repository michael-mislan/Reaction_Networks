import proofs.FiniteCopy.QuadraticCertificates
import proofs.FiniteCopy.SourceBoxes

namespace FiniteCopy
open CoreCouplingCAC Set

theorem normSq_nonneg (x : Point) : 0 ≤ normSq x := by unfold normSq; positivity
theorem coordinate_sq_le_normSq (x : Point) (i : Fin 4) : (x i)^2 ≤ normSq x := by
  fin_cases i
  all_goals first | change (x 0)^2 ≤ normSq x | change (x 1)^2 ≤ normSq x | change (x 2)^2 ≤ normSq x | change (x 3)^2 ≤ normSq x
  all_goals unfold normSq; nlinarith only [sq_nonneg (x 0),sq_nonneg (x 1),sq_nonneg (x 2),sq_nonneg (x 3)]

theorem abs_product_le_normSq (x : Point) (i j : Fin 4) : |x i*x j| ≤ normSq x := by
  rw [abs_mul]
  nlinarith [coordinate_sq_le_normSq x i,coordinate_sq_le_normSq x j,
    sq_nonneg (|x i|-|x j|),sq_abs (x i),sq_abs (x j)]

theorem small_coefficient_product (x : Point) (i j : Fin 4) (c : ℝ)
    (hc : |c| ≤ 1/100) : c*x i*x j ≤ (1/100)*normSq x := by
  calc
    c*x i*x j ≤ |c*(x i*x j)| := by rw [← mul_assoc]; exact le_abs_self _
    _ = |c| * |x i*x j| := abs_mul _ _
    _ ≤ (1/100)*normSq x := mul_le_mul hc (abs_product_le_normSq x i j) (abs_nonneg _) (by norm_num)

noncomputable def sourceLinear (A B z : ℝ) (y : Point) : Point :=
  ![(-2-4/100000*A)*y 0+(z+2/100000)*y 1+B*y 2,
    (1+2/100000*A)*y 0+(-1-z-1/100000)*y 1-B*y 2,
    y 0-z*y 1+(-B-16-8*z)*y 2+3*y 3,
    (16+4*z)*y 2+(-2-1/10000)*y 3]

noncomputable def lowPair (x v : Point) : ℝ :=
  (1115801/1000000 : ℝ)*x 0*v 0 + (-153427/250000 : ℝ)*x 0*v 1 + (2346047/1000000 : ℝ)*x 0*v 2 + (688977/200000 : ℝ)*x 0*v 3 + (-153427/250000 : ℝ)*x 1*v 0 + (1111499/1000000 : ℝ)*x 1*v 1 + (-2339313/1000000 : ℝ)*x 1*v 2 + (-214649/62500 : ℝ)*x 1*v 3 + (2346047/1000000 : ℝ)*x 2*v 0 + (-2339313/1000000 : ℝ)*x 2*v 1 + (6767757/1000000 : ℝ)*x 2*v 2 + (5089403/500000 : ℝ)*x 2*v 3 + (688977/200000 : ℝ)*x 3*v 0 + (-214649/62500 : ℝ)*x 3*v 1 + (5089403/500000 : ℝ)*x 3*v 2 + (15517433/1000000 : ℝ)*x 3*v 3

theorem lowEnergy_add (x v : Point) :
    lowEnergy (fun i => x i+v i) = lowEnergy x+2*lowPair x v+lowEnergy v := by
  unfold lowEnergy lowPair
  ring

theorem lowlinear_dissipation (A B z : ℝ) (x : Point)
    (hA : A ∈ Icc (12/1 : ℝ) (14/1 : ℝ))
    (hB : B ∈ Icc (5007/250 : ℝ) (100141/5000 : ℝ))
    (hz : z ∈ Icc (6223712577/6250000000 : ℝ) (99579401233/100000000000 : ℝ)) :
    2*lowPair x (sourceLinear A B z x) ≤ -(84/100)*normSq x := by
  have e00 : |(737/500000 : ℝ) + (-284531/2500000000 : ℝ)*A| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t00 := small_coefficient_product x 0 0 ((737/500000 : ℝ) + (-284531/2500000000 : ℝ)*A) e00
  have e01 : |(6133384531/10000000000 : ℝ) + (467783/10000000000 : ℝ)*A + (-308269/500000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t01 := small_coefficient_product x 0 1 ((6133384531/10000000000 : ℝ) + (467783/10000000000 : ℝ)*A + (-308269/500000 : ℝ)*z) e01
  have e02 : |(8658879/500000 : ℝ) + (-7031407/50000000000 : ℝ)*A + (-308269/500000 : ℝ)*B + (-1247209/250000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t02 := small_coefficient_product x 0 2 ((8658879/500000 : ℝ) + (-7031407/50000000000 : ℝ)*A + (-308269/500000 : ℝ)*B + (-1247209/250000 : ℝ)*z) e02
  have e03 : |(5357023/2000000000 : ℝ) + (-5162077/25000000000 : ℝ)*A| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t03 := small_coefficient_product x 0 3 ((5357023/2000000000 : ℝ) + (-5162077/25000000000 : ℝ)*A) e03
  have e10 : |(6133384531/10000000000 : ℝ) + (467783/10000000000 : ℝ)*A + (-308269/500000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t10 := small_coefficient_product x 1 0 ((6133384531/10000000000 : ℝ) + (467783/10000000000 : ℝ)*A + (-308269/500000 : ℝ)*z) e10
  have e11 : |(-12230447783/10000000000 : ℝ) + (307053/250000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t11 := small_coefficient_product x 1 1 ((-12230447783/10000000000 : ℝ) + (307053/250000 : ℝ)*z) e11
  have e12 : |(-1518175268593/100000000000 : ℝ) + (307053/500000 : ℝ)*B + (2894571/1000000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t12 := small_coefficient_product x 1 2 ((-1518175268593/100000000000 : ℝ) + (307053/500000 : ℝ)*B + (2894571/1000000 : ℝ)*z) e12
  have e13 : |(164282983997/50000000000 : ℝ) + (-3299537/1000000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t13 := small_coefficient_product x 1 3 ((164282983997/50000000000 : ℝ) + (-3299537/1000000 : ℝ)*z) e13
  have e20 : |(8658879/500000 : ℝ) + (-7031407/50000000000 : ℝ)*A + (-308269/500000 : ℝ)*B + (-1247209/250000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t20 := small_coefficient_product x 2 0 ((8658879/500000 : ℝ) + (-7031407/50000000000 : ℝ)*A + (-308269/500000 : ℝ)*B + (-1247209/250000 : ℝ)*z) e20
  have e21 : |(-1518175268593/100000000000 : ℝ) + (307053/500000 : ℝ)*B + (2894571/1000000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t21 := small_coefficient_product x 2 1 ((-1518175268593/100000000000 : ℝ) + (307053/500000 : ℝ)*B + (2894571/1000000 : ℝ)*z) e21
  have e22 : |(3442299/31250 : ℝ) + (-2082397/500000 : ℝ)*B + (-839177/31250 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t22 := small_coefficient_product x 2 2 ((3442299/31250 : ℝ) + (-2082397/500000 : ℝ)*B + (-839177/31250 : ℝ)*z) e22
  have e23 : |(426813365597/5000000000 : ℝ) + (-3299537/1000000 : ℝ)*B + (-4840179/250000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t23 := small_coefficient_product x 2 3 ((426813365597/5000000000 : ℝ) + (-3299537/1000000 : ℝ)*B + (-4840179/250000 : ℝ)*z) e23
  have e30 : |(5357023/2000000000 : ℝ) + (-5162077/25000000000 : ℝ)*A| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t30 := small_coefficient_product x 3 0 ((5357023/2000000000 : ℝ) + (-5162077/25000000000 : ℝ)*A) e30
  have e31 : |(164282983997/50000000000 : ℝ) + (-3299537/1000000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t31 := small_coefficient_product x 3 1 ((164282983997/50000000000 : ℝ) + (-3299537/1000000 : ℝ)*z) e31
  have e32 : |(426813365597/5000000000 : ℝ) + (-3299537/1000000 : ℝ)*B + (-4840179/250000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t32 := small_coefficient_product x 3 2 ((426813365597/5000000000 : ℝ) + (-3299537/1000000 : ℝ)*B + (-4840179/250000 : ℝ)*z) e32
  have e33 : |(2567/5000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t33 := small_coefficient_product x 3 3 ((2567/5000000000 : ℝ)) e33
  have hid : 2*lowPair x (sourceLinear A B z x) = -normSq x +
    (((737/500000 : ℝ) + (-284531/2500000000 : ℝ)*A)*x 0*x 0 + ((6133384531/10000000000 : ℝ) + (467783/10000000000 : ℝ)*A + (-308269/500000 : ℝ)*z)*x 0*x 1 + ((8658879/500000 : ℝ) + (-7031407/50000000000 : ℝ)*A + (-308269/500000 : ℝ)*B + (-1247209/250000 : ℝ)*z)*x 0*x 2 + ((5357023/2000000000 : ℝ) + (-5162077/25000000000 : ℝ)*A)*x 0*x 3 + ((6133384531/10000000000 : ℝ) + (467783/10000000000 : ℝ)*A + (-308269/500000 : ℝ)*z)*x 1*x 0 + ((-12230447783/10000000000 : ℝ) + (307053/250000 : ℝ)*z)*x 1*x 1 + ((-1518175268593/100000000000 : ℝ) + (307053/500000 : ℝ)*B + (2894571/1000000 : ℝ)*z)*x 1*x 2 + ((164282983997/50000000000 : ℝ) + (-3299537/1000000 : ℝ)*z)*x 1*x 3 + ((8658879/500000 : ℝ) + (-7031407/50000000000 : ℝ)*A + (-308269/500000 : ℝ)*B + (-1247209/250000 : ℝ)*z)*x 2*x 0 + ((-1518175268593/100000000000 : ℝ) + (307053/500000 : ℝ)*B + (2894571/1000000 : ℝ)*z)*x 2*x 1 + ((3442299/31250 : ℝ) + (-2082397/500000 : ℝ)*B + (-839177/31250 : ℝ)*z)*x 2*x 2 + ((426813365597/5000000000 : ℝ) + (-3299537/1000000 : ℝ)*B + (-4840179/250000 : ℝ)*z)*x 2*x 3 + ((5357023/2000000000 : ℝ) + (-5162077/25000000000 : ℝ)*A)*x 3*x 0 + ((164282983997/50000000000 : ℝ) + (-3299537/1000000 : ℝ)*z)*x 3*x 1 + ((426813365597/5000000000 : ℝ) + (-3299537/1000000 : ℝ)*B + (-4840179/250000 : ℝ)*z)*x 3*x 2 + ((2567/5000000000 : ℝ))*x 3*x 3) := by
    norm_num [lowPair,sourceLinear,Matrix.cons_val_two,Matrix.cons_val_three,normSq]
    ring
  rw [hid]
  linarith only [t00,t01,t02,t03,t10,t11,t12,t13,t20,t21,t22,t23,t30,t31,t32,t33]

noncomputable def highPair (x v : Point) : ℝ :=
  (211521/250000 : ℝ)*x 0*v 0 + (-115949/100000 : ℝ)*x 0*v 1 + (2352853/1000000 : ℝ)*x 0*v 2 + (1755029/500000 : ℝ)*x 0*v 3 + (-115949/100000 : ℝ)*x 1*v 0 + (1083497/250000 : ℝ)*x 1*v 1 + (-6781643/1000000 : ℝ)*x 1*v 2 + (-2558257/250000 : ℝ)*x 1*v 3 + (2352853/1000000 : ℝ)*x 2*v 0 + (-6781643/1000000 : ℝ)*x 2*v 1 + (11398763/1000000 : ℝ)*x 2*v 2 + (4305569/250000 : ℝ)*x 2*v 3 + (1755029/500000 : ℝ)*x 3*v 0 + (-2558257/250000 : ℝ)*x 3*v 1 + (4305569/250000 : ℝ)*x 3*v 2 + (26082111/1000000 : ℝ)*x 3*v 3

theorem highEnergy_add (x v : Point) :
    highEnergy (fun i => x i+v i) = highEnergy x+2*highPair x v+highEnergy v := by
  unfold highEnergy highPair
  ring

theorem highlinear_dissipation (A B z : ℝ) (x : Point)
    (hA : A ∈ Icc (20/1 : ℝ) (22/1 : ℝ))
    (hB : B ∈ Icc (120569/10000 : ℝ) (120571/10000 : ℝ))
    (hz : z ∈ Icc (37204590547/12500000000 : ℝ) (297636724377/100000000000 : ℝ)) :
    2*highPair x (sourceLinear A B z x) ≤ -(84/100)*normSq x := by
  have e00 : |(239/100000 : ℝ) + (-1425829/12500000000 : ℝ)*A| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t00 := small_coefficient_product x 0 0 ((239/100000 : ℝ) + (-1425829/12500000000 : ℝ)*A) e00
  have e01 : |(51542175829/50000000000 : ℝ) + (831621/6250000000 : ℝ)*A + (-347279/1000000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t01 := small_coefficient_product x 0 1 ((51542175829/50000000000 : ℝ) + (831621/6250000000 : ℝ)*A + (-347279/1000000 : ℝ)*z) e01
  have e02 : |(9213347/500000 : ℝ) + (-11487349/50000000000 : ℝ)*A + (-347279/1000000 : ℝ)*B + (-74728/15625 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t02 := small_coefficient_product x 0 2 ((9213347/500000 : ℝ) + (-11487349/50000000000 : ℝ)*A + (-347279/1000000 : ℝ)*B + (-74728/15625 : ℝ)*z) e02
  have e03 : |(36119971/5000000000 : ℝ) + (-2156643/6250000000 : ℝ)*A| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t03 := small_coefficient_product x 0 3 ((36119971/5000000000 : ℝ) + (-2156643/6250000000 : ℝ)*A) e03
  have e10 : |(51542175829/50000000000 : ℝ) + (831621/6250000000 : ℝ)*A + (-347279/1000000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t10 := small_coefficient_product x 1 0 ((51542175829/50000000000 : ℝ) + (831621/6250000000 : ℝ)*A + (-347279/1000000 : ℝ)*z) e10
  have e11 : |(-47925681621/6250000000 : ℝ) + (257633/100000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t11 := small_coefficient_product x 1 1 ((-47925681621/6250000000 : ℝ) + (257633/100000 : ℝ)*z) e11
  have e12 : |(-4844040212651/100000000000 : ℝ) + (257633/200000 : ℝ)*B + (2211353/200000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t12 := small_coefficient_product x 1 2 ((-4844040212651/100000000000 : ℝ) + (257633/200000 : ℝ)*B + (2211353/200000 : ℝ)*z) e12
  have e13 : |(32360471357/3125000000 : ℝ) + (-347919/100000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t13 := small_coefficient_product x 1 3 ((32360471357/3125000000 : ℝ) + (-347919/100000 : ℝ)*z) e13
  have e20 : |(9213347/500000 : ℝ) + (-11487349/50000000000 : ℝ)*A + (-347279/1000000 : ℝ)*B + (-74728/15625 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t20 := small_coefficient_product x 2 0 ((9213347/500000 : ℝ) + (-11487349/50000000000 : ℝ)*A + (-347279/1000000 : ℝ)*B + (-74728/15625 : ℝ)*z) e20
  have e21 : |(-4844040212651/100000000000 : ℝ) + (257633/200000 : ℝ)*B + (2211353/200000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t21 := small_coefficient_product x 2 1 ((-4844040212651/100000000000 : ℝ) + (257633/200000 : ℝ)*B + (2211353/200000 : ℝ)*z) e21
  have e22 : |(5854763/31250 : ℝ) + (-2264267/500000 : ℝ)*B + (-22301/500 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t22 := small_coefficient_product x 2 2 ((5854763/31250 : ℝ) + (-2264267/500000 : ℝ)*B + (-22301/500 : ℝ)*z) e22
  have e23 : |(353768436931/2500000000 : ℝ) + (-347919/100000 : ℝ)*B + (-8362441/250000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t23 := small_coefficient_product x 2 3 ((353768436931/2500000000 : ℝ) + (-347919/100000 : ℝ)*B + (-8362441/250000 : ℝ)*z) e23
  have e30 : |(36119971/5000000000 : ℝ) + (-2156643/6250000000 : ℝ)*A| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t30 := small_coefficient_product x 3 0 ((36119971/5000000000 : ℝ) + (-2156643/6250000000 : ℝ)*A) e30
  have e31 : |(32360471357/3125000000 : ℝ) + (-347919/100000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t31 := small_coefficient_product x 3 1 ((32360471357/3125000000 : ℝ) + (-347919/100000 : ℝ)*z) e31
  have e32 : |(353768436931/2500000000 : ℝ) + (-347919/100000 : ℝ)*B + (-8362441/250000 : ℝ)*z| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t32 := small_coefficient_product x 3 2 ((353768436931/2500000000 : ℝ) + (-347919/100000 : ℝ)*B + (-8362441/250000 : ℝ)*z) e32
  have e33 : |(-22111/5000000000 : ℝ)| ≤ 1/100 := by
    apply abs_le.mpr
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2,hz.1,hz.2]
  have t33 := small_coefficient_product x 3 3 ((-22111/5000000000 : ℝ)) e33
  have hid : 2*highPair x (sourceLinear A B z x) = -normSq x +
    (((239/100000 : ℝ) + (-1425829/12500000000 : ℝ)*A)*x 0*x 0 + ((51542175829/50000000000 : ℝ) + (831621/6250000000 : ℝ)*A + (-347279/1000000 : ℝ)*z)*x 0*x 1 + ((9213347/500000 : ℝ) + (-11487349/50000000000 : ℝ)*A + (-347279/1000000 : ℝ)*B + (-74728/15625 : ℝ)*z)*x 0*x 2 + ((36119971/5000000000 : ℝ) + (-2156643/6250000000 : ℝ)*A)*x 0*x 3 + ((51542175829/50000000000 : ℝ) + (831621/6250000000 : ℝ)*A + (-347279/1000000 : ℝ)*z)*x 1*x 0 + ((-47925681621/6250000000 : ℝ) + (257633/100000 : ℝ)*z)*x 1*x 1 + ((-4844040212651/100000000000 : ℝ) + (257633/200000 : ℝ)*B + (2211353/200000 : ℝ)*z)*x 1*x 2 + ((32360471357/3125000000 : ℝ) + (-347919/100000 : ℝ)*z)*x 1*x 3 + ((9213347/500000 : ℝ) + (-11487349/50000000000 : ℝ)*A + (-347279/1000000 : ℝ)*B + (-74728/15625 : ℝ)*z)*x 2*x 0 + ((-4844040212651/100000000000 : ℝ) + (257633/200000 : ℝ)*B + (2211353/200000 : ℝ)*z)*x 2*x 1 + ((5854763/31250 : ℝ) + (-2264267/500000 : ℝ)*B + (-22301/500 : ℝ)*z)*x 2*x 2 + ((353768436931/2500000000 : ℝ) + (-347919/100000 : ℝ)*B + (-8362441/250000 : ℝ)*z)*x 2*x 3 + ((36119971/5000000000 : ℝ) + (-2156643/6250000000 : ℝ)*A)*x 3*x 0 + ((32360471357/3125000000 : ℝ) + (-347919/100000 : ℝ)*z)*x 3*x 1 + ((353768436931/2500000000 : ℝ) + (-347919/100000 : ℝ)*B + (-8362441/250000 : ℝ)*z)*x 3*x 2 + ((-22111/5000000000 : ℝ))*x 3*x 3) := by
    norm_num [highPair,sourceLinear,Matrix.cons_val_two,Matrix.cons_val_three,normSq]
    ring
  rw [hid]
  linarith only [t00,t01,t02,t03,t10,t11,t12,t13,t20,t21,t22,t23,t30,t31,t32,t33]

end FiniteCopy
