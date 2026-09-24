import proofs.CompositionalMemory.PairGeometry
import proofs.CompositionalMemory.Scaling

namespace CompositionalMemory
open FiniteCopy

theorem quadratic_increment_absolute (p Q r d : ℝ)
    (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hp : p^2 ≤ 1764*r^2*d^2) (hQ : 0 ≤ Q) (hQmax : Q ≤ 42*d^2) :
    |2*p+Q| ≤ 84*r*d+42*d^2 := by
  have hrd : 0 ≤ 42*r*d := by positivity
  have habs : |p| ≤ 42*r*d := by
    apply (sq_le_sq₀ (abs_nonneg p) hrd).mp
    rw [sq_abs]
    nlinarith only [hp]
  calc
    |2*p+Q| ≤ |2*p|+|Q| := abs_add_le _ _
    _ = 2*|p|+Q := by rw [abs_mul,abs_of_nonneg hQ]; norm_num
    _ ≤ _ := by linarith only [habs,hQmax]

theorem birth_scaled_increment_small (N r d δ : ℝ)
    (hN : 1 ≤ N) (hrmax : r ≤ 1/400)
    (hd : 0 ≤ d) (hdmax : d ≤ 71/N)
    (hδ : |δ| ≤ 84*r*d+42*d^2) :
    |(1/1000000000000 : ℝ)*N*δ| ≤ 1 := by
  have hNp : 0 < N := by linarith only [hN]
  have hNd : d*N ≤ 71 := (le_div_iff₀ hNp).mp hdmax
  have hd71 : d ≤ 71 := by nlinarith only [hNd,mul_nonneg (sub_nonneg.mpr hN) hd]
  have hdsq : N*d^2 ≤ 5041 := by
    have h1 := mul_le_mul_of_nonneg_right hNd hd
    nlinarith only [h1,hd71]
  have hrNd : r*(d*N) ≤ (1/400 : ℝ)*71 :=
    mul_le_mul hrmax hNd (mul_nonneg hd hNp.le) (by norm_num)
  rw [abs_mul,abs_of_nonneg (show 0 ≤ (1/1000000000000 : ℝ)*N by positivity)]
  have hscaled := mul_le_mul_of_nonneg_left hδ
    (show 0 ≤ (1/1000000000000 : ℝ)*N by positivity)
  nlinarith only [hscaled,hdsq,hrNd]

theorem resident_jump_norm (j : Fin 13) : normSq (jump j) ≤ 5 := by
  fin_cases j <;> norm_num [normSq,jump,Matrix.cons_val_two,Matrix.cons_val_three]

theorem consuming_vector_norm (x : Point) (k : ℝ)
    (hk : 0 ≤ k) (hx : normSq x ≤ 4900) (hxz : x 2 ≤ 70) :
    normSq (fun a => x a + if a=2 then k else 0) ≤ (70+k)^2 := by
  have hid : normSq (fun a => x a + if a=2 then k else 0) =
      normSq x+2*k*x 2+k^2 := by
    norm_num [normSq, Fin.ext_iff]
    ring
  rw [hid]
  have hz := mul_le_mul_of_nonneg_left hxz (show 0 ≤ 2*k by positivity)
  nlinarith only [hx,hz]

end CompositionalMemory
