import Mathlib

namespace PowerLawSmallRAF

open scoped BigOperators

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

/-- One-coordinate expectation under a finite iid product weight. -/
theorem finiteProduct_expectation_coordinate
    (p g : Ω → ℝ) (hp : ∑ a, p a = 1) (j : I) :
    (∑ cfg : I → Ω, (∏ i, p (cfg i)) * g (cfg j)) =
      ∑ a, p a * g a := by
  have hpoint (cfg : I → Ω) :
      (∏ i, p (cfg i)) * g (cfg j) =
        ∏ i, if i = j then p (cfg i) * g (cfg i) else p (cfg i) := by
    rw [Fintype.prod_eq_mul_prod_compl j,
      Fintype.prod_eq_mul_prod_compl j]
    simp only [if_pos]
    have hcomp :
        (∏ i ∈ ({j}ᶜ : Finset I), p (cfg i)) =
          ∏ i ∈ ({j}ᶜ : Finset I),
            if i = j then p (cfg i) * g (cfg i) else p (cfg i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hij : i ≠ j := by simpa using hi
      simp [hij]
    rw [← hcomp]
    ring
  simp_rw [hpoint]
  calc
    (∑ cfg : I → Ω,
        ∏ i : I, if i = j then p (cfg i) * g (cfg i) else p (cfg i)) =
        ∏ i : I, ∑ a : Ω,
          (if i = j then p a * g a else p a) := by
      symm
      exact Fintype.prod_sum _
    _ = ∑ a, p a * g a := by
      simp [Fintype.prod_eq_mul_prod_compl j, hp]

/-- Two distinct coordinates factor under a finite iid product weight. -/
theorem finiteProduct_expectation_two_coordinates
    (p g h : Ω → ℝ) (hp : ∑ a, p a = 1)
    {i j : I} (hij : i ≠ j) :
    (∑ cfg : I → Ω,
      (∏ k, p (cfg k)) * g (cfg i) * h (cfg j)) =
      (∑ a, p a * g a) * (∑ a, p a * h a) := by
  have hpoint (cfg : I → Ω) :
      (∏ k, p (cfg k)) * g (cfg i) * h (cfg j) =
        ∏ k,
          if k = i then p (cfg k) * g (cfg k)
          else if k = j then p (cfg k) * h (cfg k)
          else p (cfg k) := by
    rw [Fintype.prod_eq_mul_prod_compl i,
      Fintype.prod_eq_mul_prod_compl i]
    simp only [if_pos]
    have hji : j ∈ ({i}ᶜ : Finset I) := by simp [Ne.symm hij]
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hji,
      Finset.prod_eq_mul_prod_diff_singleton_of_mem hji]
    simp only [Ne.symm hij, if_false, if_true]
    have hrest :
        (∏ k ∈ ({i}ᶜ : Finset I) \ {j}, p (cfg k)) =
          ∏ k ∈ ({i}ᶜ : Finset I) \ {j},
            if k = i then p (cfg k) * g (cfg k)
            else if k = j then p (cfg k) * h (cfg k)
            else p (cfg k) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hki : k ≠ i := by
        have := (Finset.mem_sdiff.mp hk).1
        simpa using this
      have hkj : k ≠ j := by
        have hnotmem : k ∉ ({j} : Finset I) := (Finset.mem_sdiff.mp hk).2
        simpa using hnotmem
      simp [hki, hkj]
    rw [← hrest]
    ring
  simp_rw [hpoint]
  calc
    (∑ cfg : I → Ω, ∏ k : I,
          if k = i then p (cfg k) * g (cfg k)
          else if k = j then p (cfg k) * h (cfg k)
          else p (cfg k)) =
        ∏ k : I, ∑ a : Ω,
          if k = i then p a * g a
          else if k = j then p a * h a
          else p a := by
      symm
      exact Fintype.prod_sum _
    _ = (∑ a, p a * g a) * (∑ a, p a * h a) := by
      rw [Fintype.prod_eq_mul_prod_compl i]
      simp only [if_pos]
      have hji : j ∈ ({i}ᶜ : Finset I) := by simp [Ne.symm hij]
      rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hji]
      simp only [Ne.symm hij, if_false, if_true]
      have hrest :
          (∏ k ∈ ({i}ᶜ : Finset I) \ {j},
            ∑ a : Ω,
              if k = i then p a * g a
              else if k = j then p a * h a
              else p a) = 1 := by
        calc
          _ = ∏ _k ∈ ({i}ᶜ : Finset I) \ {j}, (∑ a : Ω, p a) := by
            apply Finset.prod_congr rfl
            intro k hk
            have hki : k ≠ i := by
              have := (Finset.mem_sdiff.mp hk).1
              simpa using this
            have hkj : k ≠ j := by
              have hnotmem : k ∉ ({j} : Finset I) :=
                (Finset.mem_sdiff.mp hk).2
              simpa using hnotmem
            simp [hki, hkj]
          _ = 1 := by simp [hp]
      rw [hrest]
      ring

/-- Exact variance identity for a sum of iid finite-coordinate observables. -/
theorem finiteProduct_centered_sum_sq
    (p z : Ω → ℝ) (hp : ∑ a, p a = 1)
    (hz : ∑ a, p a * z a = 0) :
    (∑ cfg : I → Ω,
      (∏ i, p (cfg i)) * (∑ i, z (cfg i)) ^ 2) =
      Fintype.card I * (∑ a, p a * (z a) ^ 2) := by
  classical
  calc
    (∑ cfg : I → Ω,
        (∏ i, p (cfg i)) * (∑ i, z (cfg i)) ^ 2) =
        ∑ cfg : I → Ω, ∑ i : I, ∑ j : I,
          (∏ k, p (cfg k)) * (z (cfg i) * z (cfg j)) := by
      apply Finset.sum_congr rfl
      intro cfg hcfg
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ i : I, ∑ j : I, ∑ cfg : I → Ω,
        (∏ k, p (cfg k)) * (z (cfg i) * z (cfg j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i : I, ∑ j : I,
        if i = j then ∑ a, p a * (z a) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · subst j
        simp only [if_pos]
        simpa [mul_assoc, pow_two] using
          finiteProduct_expectation_coordinate (I := I) p (fun a => z a * z a) hp i
      · simp only [if_neg hij]
        calc
          ∑ cfg : I → Ω,
              (∏ k, p (cfg k)) * (z (cfg i) * z (cfg j)) =
              (∑ a, p a * z a) * (∑ a, p a * z a) := by
                simpa [mul_assoc] using
                  finiteProduct_expectation_two_coordinates
                    (I := I) p z z hp hij
          _ = 0 := by rw [hz, zero_mul]
    _ = Fintype.card I * (∑ a, p a * (z a) ^ 2) := by
      simp

/-- Finite-product Chebyshev bound, stated directly as a weighted bad-event
sum so it can be applied to the source configuration law without introducing
an auxiliary probability-space wrapper. -/
theorem finiteProduct_chebyshev_sq
    (p z : Ω → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp : ∑ a, p a = 1)
    (hz : ∑ a, p a * z a = 0) {eps : ℝ} (heps : 0 < eps) :
    (∑ cfg : I → Ω,
      if eps ^ 2 ≤ (∑ i, z (cfg i)) ^ 2 then ∏ i, p (cfg i) else 0) ≤
      (Fintype.card I * (∑ a, p a * (z a) ^ 2)) / eps ^ 2 := by
  have hepssq : 0 < eps ^ 2 := sq_pos_of_pos heps
  calc
    (∑ cfg : I → Ω,
      if eps ^ 2 ≤ (∑ i, z (cfg i)) ^ 2 then ∏ i, p (cfg i) else 0) ≤
        ∑ cfg : I → Ω,
          ((∏ i, p (cfg i)) * (∑ i, z (cfg i)) ^ 2) / eps ^ 2 := by
      apply Finset.sum_le_sum
      intro cfg hcfg
      by_cases hbad : eps ^ 2 ≤ (∑ i, z (cfg i)) ^ 2
      · rw [if_pos hbad]
        apply (le_div_iff₀ hepssq).2
        exact mul_le_mul_of_nonneg_left hbad
          (Finset.prod_nonneg fun i hi => hp0 (cfg i))
      · rw [if_neg hbad]
        exact div_nonneg
          (mul_nonneg (Finset.prod_nonneg fun i hi => hp0 (cfg i)) (sq_nonneg _))
          hepssq.le
    _ = (∑ cfg : I → Ω,
          (∏ i, p (cfg i)) * (∑ i, z (cfg i)) ^ 2) / eps ^ 2 := by
      rw [Finset.sum_div]
    _ = (Fintype.card I * (∑ a, p a * (z a) ^ 2)) / eps ^ 2 := by
      rw [finiteProduct_centered_sum_sq p z hp hz]

/-- A bounded nonnegative observable has centered second moment at most its
cap times its mean. -/
theorem finite_centered_secondMoment_le_cap_mul_mean
    (p y : Ω → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp : ∑ a, p a = 1)
    (hy0 : ∀ a, 0 ≤ y a) {U : ℝ} (hyU : ∀ a, y a ≤ U) :
    (∑ a, p a * (y a - ∑ b, p b * y b) ^ 2) ≤
      U * (∑ a, p a * y a) := by
  let mu : ℝ := ∑ a, p a * y a
  have hmu0 : 0 ≤ mu := by
    dsimp [mu]
    exact Finset.sum_nonneg fun a ha => mul_nonneg (hp0 a) (hy0 a)
  have hexpand :
      (∑ a, p a * (y a - mu) ^ 2) =
        (∑ a, p a * y a ^ 2) - mu ^ 2 := by
    calc
      (∑ a, p a * (y a - mu) ^ 2) =
          ∑ a, (p a * y a ^ 2 - 2 * mu * (p a * y a) + mu ^ 2 * p a) := by
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = (∑ a, p a * y a ^ 2) -
          2 * mu * (∑ a, p a * y a) + mu ^ 2 * (∑ a, p a) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
      _ = (∑ a, p a * y a ^ 2) - mu ^ 2 := by
        rw [hp]
        change (∑ a, p a * y a ^ 2) - 2 * mu * mu + mu ^ 2 * 1 = _
        ring
  rw [show (∑ b, p b * y b) = mu by rfl, hexpand]
  calc
    (∑ a, p a * y a ^ 2) - mu ^ 2 ≤
        ∑ a, p a * y a ^ 2 := by nlinarith [sq_nonneg mu]
    _ ≤ ∑ a, p a * (U * y a) := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left _ (hp0 a)
      nlinarith [hy0 a, hyU a]
    _ = U * mu := by
      dsimp [mu]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

/-- Chebyshev with the second moment eliminated in favor of a uniform cap. -/
theorem finiteProduct_bounded_chebyshev_sq
    (p y : Ω → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp : ∑ a, p a = 1)
    (hy0 : ∀ a, 0 ≤ y a) {U eps : ℝ} (hyU : ∀ a, y a ≤ U)
    (heps : 0 < eps) :
    (∑ cfg : I → Ω,
      if eps ^ 2 ≤
          (∑ i, (y (cfg i) - ∑ a, p a * y a)) ^ 2 then
        ∏ i, p (cfg i) else 0) ≤
      (Fintype.card I * U * (∑ a, p a * y a)) / eps ^ 2 := by
  let mu : ℝ := ∑ a, p a * y a
  have hz : ∑ a, p a * (y a - mu) = 0 := by
    calc
      (∑ a, p a * (y a - mu)) =
          (∑ a, p a * y a) - mu * (∑ a, p a) := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
        ring
      _ = 0 := by rw [hp]; dsimp [mu]; ring
  have hcheb := finiteProduct_chebyshev_sq (I := I) p (fun a => y a - mu)
    hp0 hp hz heps
  have hvar := finite_centered_secondMoment_le_cap_mul_mean
    p y hp0 hp hy0 hyU
  have hnum :
      Fintype.card I * (∑ a, p a * (y a - mu) ^ 2) ≤
        Fintype.card I * U * (∑ a, p a * y a) := by
    calc
      Fintype.card I * (∑ a, p a * (y a - mu) ^ 2) ≤
          Fintype.card I * (U * (∑ a, p a * y a)) :=
        mul_le_mul_of_nonneg_left (by simpa [mu] using hvar) (by positivity)
      _ = Fintype.card I * U * (∑ a, p a * y a) := by ring
  exact hcheb.trans (div_le_div_of_nonneg_right hnum (sq_nonneg eps))

end PowerLawSmallRAF
