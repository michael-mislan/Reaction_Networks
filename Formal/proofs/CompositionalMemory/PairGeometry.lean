import proofs.FiniteCopy.JumpNoise

namespace CompositionalMemory
open FiniteCopy

theorem low_pair_squared_bound (y v : Point) :
    (lowPair y v)^2 ≤ 1764*normSq y*normSq v := by
  let c0 : ℝ := (1115801/1000000 : ℝ)*y 0+(-613708/1000000 : ℝ)*y 1+(2346047/1000000 : ℝ)*y 2+(3444885/1000000 : ℝ)*y 3
  have h0 := linear_four_sq (1115801/1000000 : ℝ) (-613708/1000000 : ℝ) (2346047/1000000 : ℝ) (3444885/1000000 : ℝ) y
  let c1 : ℝ := (-613708/1000000 : ℝ)*y 0+(1111499/1000000 : ℝ)*y 1+(-2339313/1000000 : ℝ)*y 2+(-3434384/1000000 : ℝ)*y 3
  have h1 := linear_four_sq (-613708/1000000 : ℝ) (1111499/1000000 : ℝ) (-2339313/1000000 : ℝ) (-3434384/1000000 : ℝ) y
  let c2 : ℝ := (2346047/1000000 : ℝ)*y 0+(-2339313/1000000 : ℝ)*y 1+(6767757/1000000 : ℝ)*y 2+(10178806/1000000 : ℝ)*y 3
  have h2 := linear_four_sq (2346047/1000000 : ℝ) (-2339313/1000000 : ℝ) (6767757/1000000 : ℝ) (10178806/1000000 : ℝ) y
  let c3 : ℝ := (3444885/1000000 : ℝ)*y 0+(-3434384/1000000 : ℝ)*y 1+(10178806/1000000 : ℝ)*y 2+(15517433/1000000 : ℝ)*y 3
  have h3 := linear_four_sq (3444885/1000000 : ℝ) (-3434384/1000000 : ℝ) (10178806/1000000 : ℝ) (15517433/1000000 : ℝ) y
  have hv := linear_four_sq c0 c1 c2 c3 v
  have hid : lowPair y v = c0*v 0+c1*v 1+c2*v 2+c3*v 3 := by
    dsimp [c0,c1,c2,c3,lowPair]
    ring
  have hs : c0^2+c1^2+c2^2+c3^2 ≤ 1764*normSq y := by
    dsimp [c0,c1,c2,c3]
    norm_num only at h0 h1 h2 h3
    nlinarith only [h0,h1,h2,h3,normSq_nonneg y]
  rw [← hid] at hv
  exact hv.trans (mul_le_mul_of_nonneg_right hs (normSq_nonneg v))

theorem high_pair_squared_bound (y v : Point) :
    (highPair y v)^2 ≤ 1764*normSq y*normSq v := by
  let c0 : ℝ := (846084/1000000 : ℝ)*y 0+(-1159490/1000000 : ℝ)*y 1+(2352853/1000000 : ℝ)*y 2+(3510058/1000000 : ℝ)*y 3
  have h0 := linear_four_sq (846084/1000000 : ℝ) (-1159490/1000000 : ℝ) (2352853/1000000 : ℝ) (3510058/1000000 : ℝ) y
  let c1 : ℝ := (-1159490/1000000 : ℝ)*y 0+(4333988/1000000 : ℝ)*y 1+(-6781643/1000000 : ℝ)*y 2+(-10233028/1000000 : ℝ)*y 3
  have h1 := linear_four_sq (-1159490/1000000 : ℝ) (4333988/1000000 : ℝ) (-6781643/1000000 : ℝ) (-10233028/1000000 : ℝ) y
  let c2 : ℝ := (2352853/1000000 : ℝ)*y 0+(-6781643/1000000 : ℝ)*y 1+(11398763/1000000 : ℝ)*y 2+(17222276/1000000 : ℝ)*y 3
  have h2 := linear_four_sq (2352853/1000000 : ℝ) (-6781643/1000000 : ℝ) (11398763/1000000 : ℝ) (17222276/1000000 : ℝ) y
  let c3 : ℝ := (3510058/1000000 : ℝ)*y 0+(-10233028/1000000 : ℝ)*y 1+(17222276/1000000 : ℝ)*y 2+(26082111/1000000 : ℝ)*y 3
  have h3 := linear_four_sq (3510058/1000000 : ℝ) (-10233028/1000000 : ℝ) (17222276/1000000 : ℝ) (26082111/1000000 : ℝ) y
  have hv := linear_four_sq c0 c1 c2 c3 v
  have hid : highPair y v = c0*v 0+c1*v 1+c2*v 2+c3*v 3 := by
    dsimp [c0,c1,c2,c3,highPair]
    ring
  have hs : c0^2+c1^2+c2^2+c3^2 ≤ 1764*normSq y := by
    dsimp [c0,c1,c2,c3]
    norm_num only at h0 h1 h2 h3
    nlinarith only [h0,h1,h2,h3,normSq_nonneg y]
  rw [← hid] at hv
  exact hv.trans (mul_le_mul_of_nonneg_right hs (normSq_nonneg v))

end CompositionalMemory
