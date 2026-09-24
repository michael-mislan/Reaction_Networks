import proofs.FiniteCopy.LocalGenerator
import proofs.HeritableCompositions.ExponentialScaling

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

theorem source_generator_scaled (e : ℝ) (he : 0 ≤ e)
    (N m : ℕ) (hm : 1 ≤ m) (hNm : N ≤ m) (n : Counts) (E : Point → ℝ) :
    generator e m (fun x => Real.exp ((N : ℝ)*E x)) (concentration m n) ≤
      ((N : ℝ)/(m : ℝ))*Real.exp (((N : ℝ)-(m : ℝ))*E (concentration m n))*
        generator e m (fun x => Real.exp ((m : ℝ)*E x)) (concentration m n) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hNm' : (N : ℝ) ≤ m := by exact_mod_cast hNm
  let x := concentration m n
  let c := ((N : ℝ)/(m : ℝ))*Real.exp (((N : ℝ)-(m : ℝ))*E x)
  have hpoint (r : Fin 13) :
      densityRates e (1/(m : ℝ)) x r*
        (Real.exp ((N : ℝ)*E (fun i => x i+jump r i/(m : ℝ)))-Real.exp ((N : ℝ)*E x)) ≤
      c*(densityRates e (1/(m : ℝ)) x r*
        (Real.exp ((m : ℝ)*E (fun i => x i+jump r i/(m : ℝ)))-Real.exp ((m : ℝ)*E x))) := by
    have hh := mul_le_mul_of_nonneg_left
      (exp_two_scale_increment (N : ℝ) (m : ℝ) (E x)
        (E (fun i => x i+jump r i/(m : ℝ))) (Nat.cast_nonneg N) hmpos hNm')
      (lattice_rates_nonneg e he m n r)
    dsimp [c]
    nlinarith only [hh]
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hpoint r))
    (Nat.cast_nonneg m)
  unfold generator
  dsimp [x,c] at hh
  rw [← Finset.mul_sum] at hh
  nlinarith only [hh]

theorem source_scaled_bound (e : ℝ) (he : 0 ≤ e)
    (N m : ℕ) (hm : 1 ≤ m) (hNm : N ≤ m) (n : Counts) (E : Point → ℝ) (b : ℝ)
    (hsource : generator e m (fun x => Real.exp ((m : ℝ)*E x)) (concentration m n) ≤
      Real.exp ((m : ℝ)*E (concentration m n))*b) :
    generator e m (fun x => Real.exp ((N : ℝ)*E x)) (concentration m n) ≤
      ((N : ℝ)/(m : ℝ))*Real.exp ((N : ℝ)*E (concentration m n))*b := by
  let x := concentration m n
  have h := source_generator_scaled e he N m hm hNm n E
  have hh := mul_le_mul_of_nonneg_left hsource (by positivity :
    0 ≤ ((N : ℝ)/(m : ℝ))*Real.exp (((N : ℝ)-(m : ℝ))*E x))
  have heq : Real.exp (((N : ℝ)-(m : ℝ))*E x)*Real.exp ((m : ℝ)*E x) =
      Real.exp ((N : ℝ)*E x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    generator e m (fun x => Real.exp ((N : ℝ)*E x)) x ≤
      ((N : ℝ)/(m : ℝ))*Real.exp (((N : ℝ)-(m : ℝ))*E x)*
        (Real.exp ((m : ℝ)*E x)*b) := h.trans hh
    _ = ((N : ℝ)/(m : ℝ))*(Real.exp (((N : ℝ)-(m : ℝ))*E x)*
        Real.exp ((m : ℝ)*E x))*b := by ring
    _ = _ := by rw [heq]

theorem source_scaled_dissipation (e α v B : ℝ) (he : 0 ≤ e)
    (hα : 0 ≤ α) (hB : 0 ≤ B) (N m : ℕ) (hm : 1 ≤ m) (hNm : N ≤ m)
    (n : Counts) (E : Point → ℝ)
    (hsource : generator e m (fun x => Real.exp ((m : ℝ)*(α*E x))) (concentration m n) ≤
      Real.exp ((m : ℝ)*(α*E (concentration m n)))*(α*(-(m : ℝ)/2*v+B))) :
    generator e m (fun x => Real.exp ((N : ℝ)*(α*E x))) (concentration m n) ≤
      Real.exp ((N : ℝ)*(α*E (concentration m n)))*(α*(-(N : ℝ)/2*v+B)) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hratio : (N : ℝ)/(m : ℝ) ≤ 1 :=
    (div_le_one hmpos).mpr (by exact_mod_cast hNm)
  have h := source_scaled_bound e he N m hm hNm n (fun x => α*E x)
    (α*(-(m : ℝ)/2*v+B)) hsource
  have hid : ((N : ℝ)/(m : ℝ))*Real.exp ((N : ℝ)*(α*E (concentration m n)))*
      (α*(-(m : ℝ)/2*v+B)) =
      Real.exp ((N : ℝ)*(α*E (concentration m n)))*(α*(-(N : ℝ)/2*v+B*((N : ℝ)/(m : ℝ)))) := by
    field_simp
  rw [hid] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left _ hα
  have hh := mul_le_mul_of_nonneg_left hratio hB
  linarith only [hh]

end HeritableCompositions
