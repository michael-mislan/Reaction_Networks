import proofs.FiniteCopy.QuadraticCertificates

namespace FiniteCopy

theorem lowEnergy_scale (c : ℝ) (y : Point) :
    lowEnergy (fun i => c*y i) = c^2*lowEnergy y := by
  unfold lowEnergy
  ring

theorem lowinitial_box_energy (u : Point) (h0 : 6999 ≤ u 0 ∧ u 0 ≤ 7000)
    (h1 : |u 1| ≤ 1) (h2 : |u 2| ≤ 1) (h3 : |u 3| ≤ 1) :
    39062500 ≤ lowEnergy u ∧ lowEnergy u ≤ 78125000 := by
  have h0a : |u 0| ≤ 7000 := abs_le.mpr ⟨by linarith [h0.1],h0.2⟩
  have hdiag : (6999:ℝ)^2 ≤ (u 0)^2 ∧ (u 0)^2 ≤ (7000:ℝ)^2 := by
    constructor <;> nlinarith only [h0.1,h0.2]
  have t01 : |(-153427/125000 : ℝ)*u 0*u 1| ≤ 100000 := by
    calc
      _ = |(-153427/125000 : ℝ)| * (|u 0| * |u 1|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(-153427/125000 : ℝ)| * 7000 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h0a h1 (abs_nonneg (u 1)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t01b := abs_le.mp t01
  have t02 : |(2346047/500000 : ℝ)*u 0*u 2| ≤ 100000 := by
    calc
      _ = |(2346047/500000 : ℝ)| * (|u 0| * |u 2|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(2346047/500000 : ℝ)| * 7000 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h0a h2 (abs_nonneg (u 2)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t02b := abs_le.mp t02
  have t03 : |(688977/100000 : ℝ)*u 0*u 3| ≤ 100000 := by
    calc
      _ = |(688977/100000 : ℝ)| * (|u 0| * |u 3|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(688977/100000 : ℝ)| * 7000 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h0a h3 (abs_nonneg (u 3)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t03b := abs_le.mp t03
  have t11 : |(1111499/1000000 : ℝ)*u 1*u 1| ≤ 100000 := by
    calc
      _ = |(1111499/1000000 : ℝ)| * (|u 1| * |u 1|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(1111499/1000000 : ℝ)| * 1 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h1 h1 (abs_nonneg (u 1)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t11b := abs_le.mp t11
  have t12 : |(-2339313/500000 : ℝ)*u 1*u 2| ≤ 100000 := by
    calc
      _ = |(-2339313/500000 : ℝ)| * (|u 1| * |u 2|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(-2339313/500000 : ℝ)| * 1 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h1 h2 (abs_nonneg (u 2)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t12b := abs_le.mp t12
  have t13 : |(-214649/31250 : ℝ)*u 1*u 3| ≤ 100000 := by
    calc
      _ = |(-214649/31250 : ℝ)| * (|u 1| * |u 3|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(-214649/31250 : ℝ)| * 1 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h1 h3 (abs_nonneg (u 3)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t13b := abs_le.mp t13
  have t22 : |(6767757/1000000 : ℝ)*u 2*u 2| ≤ 100000 := by
    calc
      _ = |(6767757/1000000 : ℝ)| * (|u 2| * |u 2|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(6767757/1000000 : ℝ)| * 1 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h2 h2 (abs_nonneg (u 2)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t22b := abs_le.mp t22
  have t23 : |(5089403/250000 : ℝ)*u 2*u 3| ≤ 100000 := by
    calc
      _ = |(5089403/250000 : ℝ)| * (|u 2| * |u 3|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(5089403/250000 : ℝ)| * 1 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h2 h3 (abs_nonneg (u 3)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t23b := abs_le.mp t23
  have t33 : |(15517433/1000000 : ℝ)*u 3*u 3| ≤ 100000 := by
    calc
      _ = |(15517433/1000000 : ℝ)| * (|u 3| * |u 3|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(15517433/1000000 : ℝ)| * 1 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h3 h3 (abs_nonneg (u 3)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t33b := abs_le.mp t33
  unfold lowEnergy
  constructor <;> nlinarith only [hdiag.1,hdiag.2,t01b.1,t01b.2,t02b.1,t02b.2,t03b.1,t03b.2,t11b.1,t11b.2,t12b.1,t12b.2,t13b.1,t13b.2,t22b.1,t22b.2,t23b.1,t23b.2,t33b.1,t33b.2]

theorem lowinitial_energy (y : Point)
    (h0 : 6999/1000000000000 ≤ y 0 ∧ y 0 ≤ 7/1000000000)
    (h1 : |y 1| ≤ 1/1000000000000) (h2 : |y 2| ≤ 1/1000000000000) (h3 : |y 3| ≤ 1/1000000000000) :
    2/51200000000000000 ≤ lowEnergy y ∧ lowEnergy y ≤ 4/51200000000000000 := by
  let u : Point := fun i => 1000000000000*y i
  have h := lowinitial_box_energy u
    (by constructor <;> dsimp [u] <;> linarith [h0.1,h0.2])
    (by dsimp [u]; rw [abs_mul]; norm_num; nlinarith only [h1])
    (by dsimp [u]; rw [abs_mul]; norm_num; nlinarith only [h2])
    (by dsimp [u]; rw [abs_mul]; norm_num; nlinarith only [h3])
  have he := lowEnergy_scale 1000000000000 y
  dsimp [u] at h
  rw [he] at h
  constructor <;> nlinarith only [h.1,h.2]

theorem highEnergy_scale (c : ℝ) (y : Point) :
    highEnergy (fun i => c*y i) = c^2*highEnergy y := by
  unfold highEnergy
  ring

theorem highinitial_box_energy (u : Point) (h0 : 6999 ≤ u 0 ∧ u 0 ≤ 7000)
    (h1 : |u 1| ≤ 1) (h2 : |u 2| ≤ 1) (h3 : |u 3| ≤ 1) :
    39062500 ≤ highEnergy u ∧ highEnergy u ≤ 78125000 := by
  have h0a : |u 0| ≤ 7000 := abs_le.mpr ⟨by linarith [h0.1],h0.2⟩
  have hdiag : (6999:ℝ)^2 ≤ (u 0)^2 ∧ (u 0)^2 ≤ (7000:ℝ)^2 := by
    constructor <;> nlinarith only [h0.1,h0.2]
  have t01 : |(-115949/50000 : ℝ)*u 0*u 1| ≤ 100000 := by
    calc
      _ = |(-115949/50000 : ℝ)| * (|u 0| * |u 1|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(-115949/50000 : ℝ)| * 7000 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h0a h1 (abs_nonneg (u 1)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t01b := abs_le.mp t01
  have t02 : |(2352853/500000 : ℝ)*u 0*u 2| ≤ 100000 := by
    calc
      _ = |(2352853/500000 : ℝ)| * (|u 0| * |u 2|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(2352853/500000 : ℝ)| * 7000 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h0a h2 (abs_nonneg (u 2)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t02b := abs_le.mp t02
  have t03 : |(1755029/250000 : ℝ)*u 0*u 3| ≤ 100000 := by
    calc
      _ = |(1755029/250000 : ℝ)| * (|u 0| * |u 3|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(1755029/250000 : ℝ)| * 7000 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h0a h3 (abs_nonneg (u 3)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t03b := abs_le.mp t03
  have t11 : |(1083497/250000 : ℝ)*u 1*u 1| ≤ 100000 := by
    calc
      _ = |(1083497/250000 : ℝ)| * (|u 1| * |u 1|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(1083497/250000 : ℝ)| * 1 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h1 h1 (abs_nonneg (u 1)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t11b := abs_le.mp t11
  have t12 : |(-6781643/500000 : ℝ)*u 1*u 2| ≤ 100000 := by
    calc
      _ = |(-6781643/500000 : ℝ)| * (|u 1| * |u 2|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(-6781643/500000 : ℝ)| * 1 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h1 h2 (abs_nonneg (u 2)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t12b := abs_le.mp t12
  have t13 : |(-2558257/125000 : ℝ)*u 1*u 3| ≤ 100000 := by
    calc
      _ = |(-2558257/125000 : ℝ)| * (|u 1| * |u 3|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(-2558257/125000 : ℝ)| * 1 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h1 h3 (abs_nonneg (u 3)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t13b := abs_le.mp t13
  have t22 : |(11398763/1000000 : ℝ)*u 2*u 2| ≤ 100000 := by
    calc
      _ = |(11398763/1000000 : ℝ)| * (|u 2| * |u 2|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(11398763/1000000 : ℝ)| * 1 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h2 h2 (abs_nonneg (u 2)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t22b := abs_le.mp t22
  have t23 : |(4305569/125000 : ℝ)*u 2*u 3| ≤ 100000 := by
    calc
      _ = |(4305569/125000 : ℝ)| * (|u 2| * |u 3|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(4305569/125000 : ℝ)| * 1 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h2 h3 (abs_nonneg (u 3)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t23b := abs_le.mp t23
  have t33 : |(26082111/1000000 : ℝ)*u 3*u 3| ≤ 100000 := by
    calc
      _ = |(26082111/1000000 : ℝ)| * (|u 3| * |u 3|) := by rw [abs_mul,abs_mul]; ring
      _ ≤ |(26082111/1000000 : ℝ)| * 1 := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul h3 h3 (abs_nonneg (u 3)) (by norm_num)) (abs_nonneg _)
      _ ≤ 100000 := by norm_num
  have t33b := abs_le.mp t33
  unfold highEnergy
  constructor <;> nlinarith only [hdiag.1,hdiag.2,t01b.1,t01b.2,t02b.1,t02b.2,t03b.1,t03b.2,t11b.1,t11b.2,t12b.1,t12b.2,t13b.1,t13b.2,t22b.1,t22b.2,t23b.1,t23b.2,t33b.1,t33b.2]

theorem highinitial_energy (y : Point)
    (h0 : 6999/1000000000000 ≤ y 0 ∧ y 0 ≤ 7/1000000000)
    (h1 : |y 1| ≤ 1/1000000000000) (h2 : |y 2| ≤ 1/1000000000000) (h3 : |y 3| ≤ 1/1000000000000) :
    2/51200000000000000 ≤ highEnergy y ∧ highEnergy y ≤ 4/51200000000000000 := by
  let u : Point := fun i => 1000000000000*y i
  have h := highinitial_box_energy u
    (by constructor <;> dsimp [u] <;> linarith [h0.1,h0.2])
    (by dsimp [u]; rw [abs_mul]; norm_num; nlinarith only [h1])
    (by dsimp [u]; rw [abs_mul]; norm_num; nlinarith only [h2])
    (by dsimp [u]; rw [abs_mul]; norm_num; nlinarith only [h3])
  have he := highEnergy_scale 1000000000000 y
  dsimp [u] at h
  rw [he] at h
  constructor <;> nlinarith only [h.1,h.2]

end FiniteCopy
