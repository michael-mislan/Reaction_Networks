import proofs.RAF1519.Reservoir.CommunityEnergy

namespace RAF1519.Reservoir
noncomputable section
open scoped BigOperators

theorem core_nonnegative (P : Matrix (Fin 6) (Fin 6) ℝ)
    (hP : ∀ y, (1/1000:ℝ)*(∑ i, (y i)^2) ≤ quadratic P y) (y : Fin 6 → ℝ) :
    0 ≤ quadratic P y := by
  have hn : 0 ≤ ∑ i, (y i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  nlinarith [hP y]

theorem core_coordinate_bound (P : Matrix (Fin 6) (Fin 6) ℝ)
    (hP : ∀ y, (1/1000:ℝ)*(∑ i, (y i)^2) ≤ quadratic P y) (y : Fin 6 → ℝ) (i : Fin 6) :
    (y i)^2 ≤ 1000*quadratic P y := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
  nlinarith [hP y]

theorem weighted_deviation_square (q a y : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (q*(a+y))^2 ≤ 2*a^2+2*q*y^2 := by
  have hq2 : q^2 ≤ q := by nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
  have h1 := mul_nonneg (sub_nonneg.mpr (hq2.trans hq1)) (sq_nonneg a)
  have h2 := mul_nonneg (sub_nonneg.mpr hq2) (sq_nonneg y)
  have h3 := mul_nonneg (sq_nonneg q) (sq_nonneg (a-y))
  nlinarith only [h1,h2,h3]

theorem communityEnergy_nonnegative {n : ℕ} (P : Matrix (Fin 6) (Fin 6) ℝ)
    (q : Fin n → ℝ) (hpos : ∀ i, 0 < q i) (s : ℝ) (x : Community n)
    (hP : ∀ y, (1/1000:ℝ)*(∑ i, (y i)^2) ≤ quadratic P y) :
    0 ≤ communityEnergy P q s x := by
  exact add_nonneg (core_nonnegative P hP _) (mul_nonneg (by norm_num)
    (variance_nonnegative q _ (fun i => (hpos i).le)))

theorem communityEnergy_coercive {n : ℕ} (P : Matrix (Fin 6) (Fin 6) ℝ)
    (q : Fin n → ℝ) (hq : ∑ i, q i = 1) (hpos : ∀ i, 0 < q i) (s : ℝ)
    (hP : ∀ y, (1/1000:ℝ)*(∑ i, (y i)^2) ≤ quadratic P y)
    (x : Community n) (i : Fin 5 ⊕ Fin n) :
    (x i-lift q s i)^2 ≤ 2000*communityEnergy P q s x := by
  let E := quadratic P (aggregate x-state s)
  let y := normalizedDeviation q x
  let V := variance q y
  have hE : 0 ≤ E := core_nonnegative P hP _
  have hV : 0 ≤ V := variance_nonnegative q y (fun j => (hpos j).le)
  have hcore (j : Fin 6) : ((aggregate x-state s) j)^2 ≤ 1000*E :=
    core_coordinate_bound P hP _ j
  cases i with
  | inl i =>
    have h := hcore i.castSucc
    change (aggregate x i.castSucc-state s i.castSucc)^2 ≤ 1000*E at h
    rw [aggregate_coordinate] at h
    change (x (.inl i)-state s i.castSucc)^2 ≤ 2000*(E+100*V)
    nlinarith
  | inr i =>
    have hqi : q i ≤ 1 := by
      rw [← hq]
      exact Finset.single_le_sum (fun j _ => (hpos j).le) (Finset.mem_univ i)
    have hs := hcore 5
    change (totalConsumers x-s)^2 ≤ 1000*E at hs
    have hv : q i*(y i)^2 ≤ V :=
      Finset.single_le_sum (fun j _ => mul_nonneg (hpos j).le (sq_nonneg (y j))) (Finset.mem_univ i)
    have hi : x (.inr i)-q i*s = q i*(totalConsumers x-s+y i) := by
      have hr := consumer_reconstruction q x hpos i
      change q i*(totalConsumers x+y i) = x (.inr i) at hr
      nlinarith
    change (x (.inr i)-q i*s)^2 ≤ 2000*(E+100*V)
    rw [hi]
    have hw := weighted_deviation_square (q i) (totalConsumers x-s) (y i) (hpos i).le hqi
    nlinarith

end
end RAF1519.Reservoir
