import proofs.PowerLawSmallRAF.GatewayMarks

namespace PowerLawSmallRAF

open Filter Topology

/-- The capped Zipf degree mass for `D = min(K,R)-1`. -/
noncomputable def cappedZipfDegreeMass (a : ℝ) (R d : Nat) : ℝ :=
  if d + 1 < R then (d + 1 : ℝ) ^ (-a) / zipfNormalizer a
  else if d + 1 = R then rpowTail a R / zipfNormalizer a
  else 0

/-- Conditional probability that a uniformly chosen `d`-subset of the `R`
reactions avoids a fixed gateway set of cardinality `M`. -/
noncomputable def hypergeometricGatewayMiss (R M d : Nat) : ℝ :=
  (Nat.choose (R - M) d : ℝ) / Nat.choose R d

noncomputable def gatewayMissProduct (R M d : Nat) : ℝ :=
  ∏ j ∈ Finset.range M,
    (((R - d - j : Nat) : ℝ) / (R - j : Nat))

theorem hypergeometricGatewayMiss_eq_symmetricChoose
    (R M d : Nat) (h : d + M ≤ R) :
    hypergeometricGatewayMiss R M d =
      (Nat.choose (R - d) M : ℝ) / Nat.choose R M := by
  have hd : d ≤ R := by omega
  have hM : M ≤ R := by omega
  have hdsub : d ≤ R - M := by omega
  have hcross : Nat.choose (R - M) d * Nat.choose R M =
      Nat.choose (R - d) M * Nat.choose R d := by
    have h1 := Nat.choose_mul (n := R) (k := d + M) (s := d) (by omega)
    have h2 := Nat.choose_mul (n := R) (k := d + M) (s := M) (by omega)
    have h1' : Nat.choose R (d + M) * Nat.choose (d + M) d =
        Nat.choose R d * Nat.choose (R - d) M := by
      rw [show d + M - d = M by omega] at h1
      exact h1
    have h2' : Nat.choose R (d + M) * Nat.choose (d + M) M =
        Nat.choose R M * Nat.choose (R - M) d := by
      rw [show d + M - M = d by omega] at h2
      exact h2
    have hsym : Nat.choose (d + M) d = Nat.choose (d + M) M := by
      simpa only [Nat.add_comm] using (Nat.choose_symm_add (a := d) (b := M))
    rw [hsym] at h1'
    calc
      Nat.choose (R - M) d * Nat.choose R M =
          Nat.choose R M * Nat.choose (R - M) d := mul_comm _ _
      _ = Nat.choose R (d + M) * Nat.choose (d + M) M := h2'.symm
      _ = Nat.choose R d * Nat.choose (R - d) M := h1'
      _ = Nat.choose (R - d) M * Nat.choose R d := mul_comm _ _
  dsimp [hypergeometricGatewayMiss]
  have hden1 : (Nat.choose R d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hd))
  have hden2 : (Nat.choose R M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hM))
  field_simp [hden1, hden2]
  have hcross' : Nat.choose (R - M) d * Nat.choose R M =
      Nat.choose R d * Nat.choose (R - d) M := by
    simpa only [mul_comm] using hcross
  exact_mod_cast hcross'

theorem symmetricChooseRatio_eq_gatewayMissProduct
    (R M d : Nat) (h : d + M ≤ R) :
    (Nat.choose (R - d) M : ℝ) / Nat.choose R M =
      gatewayMissProduct R M d := by
  induction M with
  | zero => simp [gatewayMissProduct]
  | succ M ih =>
      have hprev : d + M ≤ R := by omega
      have hMd : M ≤ R - d := by omega
      have hMR : M ≤ R := by omega
      have hMd' : M + 1 ≤ R - d := by omega
      have hMR' : M + 1 ≤ R := by omega
      have hnum := Nat.choose_succ_right_eq (R - d) M
      have hden := Nat.choose_succ_right_eq R M
      rw [gatewayMissProduct, Finset.prod_range_succ, ← gatewayMissProduct,
        ← ih hprev]
      have hn0 : (Nat.choose (R - d) M : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hMd))
      have hd0 : (Nat.choose R M : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hMR))
      have hn1 : (Nat.choose (R - d) (M + 1) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hMd'))
      have hd1 : (Nat.choose R (M + 1) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hMR'))
      have hM1 : ((M + 1 : Nat) : ℝ) ≠ 0 := by positivity
      have hRM : (((R - M : Nat) : ℝ)) ≠ 0 := by
        have : 0 < R - M := by omega
        exact_mod_cast (Nat.ne_of_gt this)
      have hnumR : (Nat.choose (R - d) (M + 1) : ℝ) * (M + 1 : Nat) =
          (Nat.choose (R - d) M : ℝ) * (R - d - M : Nat) := by
        exact_mod_cast hnum
      have hdenR : (Nat.choose R (M + 1) : ℝ) * (M + 1 : Nat) =
          (Nat.choose R M : ℝ) * (R - M : Nat) := by
        exact_mod_cast hden
      calc
        (Nat.choose (R - d) (M + 1) : ℝ) / Nat.choose R (M + 1) =
            ((Nat.choose (R - d) (M + 1) : ℝ) * (M + 1 : Nat)) /
              ((Nat.choose R (M + 1) : ℝ) * (M + 1 : Nat)) := by
                field_simp [hM1, hd1]
        _ = ((Nat.choose (R - d) M : ℝ) * (R - d - M : Nat)) /
              ((Nat.choose R M : ℝ) * (R - M : Nat)) := by rw [hnumR, hdenR]
        _ = ((Nat.choose (R - d) M : ℝ) / Nat.choose R M) *
              (((R - d - M : Nat) : ℝ) / (R - M : Nat)) := by
                simp only [div_eq_mul_inv]
                ring

theorem hypergeometricGatewayMiss_eq_product
    (R M d : Nat) (h : d + M ≤ R) :
    hypergeometricGatewayMiss R M d = gatewayMissProduct R M d :=
  (hypergeometricGatewayMiss_eq_symmetricChoose R M d h).trans
    (symmetricChooseRatio_eq_gatewayMissProduct R M d h)

/-- A second-order Bonferroni bound written purely as a finite-product
identity.  It is the analytic engine for showing that one molecule hitting two
fixed gateways is asymptotically negligible. -/
theorem one_sub_prod_one_sub_bounds {α : Type*} [DecidableEq α]
    (s : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) :
    let S := ∑ i ∈ s, x i
    let H := 1 - ∏ i ∈ s, (1 - x i)
    0 ≤ H ∧ H ≤ S ∧ S - S ^ 2 ≤ H := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hxa0 : 0 ≤ x a := hx0 a (Finset.mem_insert_self a s)
      have hxa1 : x a ≤ 1 := hx1 a (Finset.mem_insert_self a s)
      have hxs0 : ∀ i ∈ s, 0 ≤ x i := by
        intro i hi
        exact hx0 i (Finset.mem_insert_of_mem hi)
      have hxs1 : ∀ i ∈ s, x i ≤ 1 := by
        intro i hi
        exact hx1 i (Finset.mem_insert_of_mem hi)
      have hi := ih hxs0 hxs1
      let S : ℝ := ∑ i ∈ s, x i
      let H : ℝ := 1 - ∏ i ∈ s, (1 - x i)
      have hH0 : 0 ≤ H := hi.1
      have hHS : H ≤ S := hi.2.1
      have hlow : S - S ^ 2 ≤ H := hi.2.2
      have hS0 : 0 ≤ S := Finset.sum_nonneg hxs0
      have hmul : H * x a ≤ S * x a :=
        mul_le_mul_of_nonneg_right hHS hxa0
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hid : 1 - (1 - x a) * ∏ i ∈ s, (1 - x i) =
          H + x a - H * x a := by
        dsimp [H]
        ring
      rw [hid]
      constructor
      · nlinarith [mul_nonneg hH0 (sub_nonneg.mpr hxa1)]
      constructor
      · nlinarith [mul_nonneg hH0 hxa0]
      · nlinarith [mul_nonneg hS0 hxa0, sq_nonneg (x a)]

noncomputable def gatewayMarginalSum (R M d : Nat) : ℝ :=
  ∑ j ∈ Finset.range M, (d : ℝ) / (R - j : Nat)

theorem hypergeometricGatewayHit_lowDegree_bounds
    (R M d : Nat) (h : d + M ≤ R) :
    let S := gatewayMarginalSum R M d
    S - S ^ 2 ≤ 1 - hypergeometricGatewayMiss R M d ∧
      1 - hypergeometricGatewayMiss R M d ≤ S := by
  have hx0 : ∀ j ∈ Finset.range M,
      0 ≤ (d : ℝ) / (R - j : Nat) := by
    intro j hj
    exact div_nonneg (by positivity) (by positivity)
  have hx1 : ∀ j ∈ Finset.range M,
      (d : ℝ) / (R - j : Nat) ≤ 1 := by
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    have hdj : d ≤ R - j := by omega
    have hden : (0 : ℝ) < (R - j : Nat) := by
      have : 0 < R - j := by omega
      exact_mod_cast this
    exact (div_le_one hden).2 (by exact_mod_cast hdj)
  have hprod : gatewayMissProduct R M d =
      ∏ j ∈ Finset.range M, (1 - (d : ℝ) / (R - j : Nat)) := by
    dsimp [gatewayMissProduct]
    apply Finset.prod_congr rfl
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    have hdj : d ≤ R - j := by omega
    have hRj : (((R - j : Nat) : ℝ)) ≠ 0 := by
      have hpos : 0 < R - j := by omega
      exact_mod_cast (Nat.ne_of_gt hpos)
    have hswap : R - d - j = R - j - d := by omega
    rw [hswap, Nat.cast_sub hdj, Nat.cast_sub (by omega : j ≤ R)]
    have hRjReal : (R : ℝ) - (j : ℝ) ≠ 0 := by
      have hjR : (j : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : j < R)
      exact sub_ne_zero.mpr (ne_of_gt hjR)
    field_simp [hRjReal]
  have hb := one_sub_prod_one_sub_bounds (Finset.range M)
    (fun j => (d : ℝ) / (R - j : Nat)) hx0 hx1
  rw [hypergeometricGatewayMiss_eq_product R M d h, hprod]
  dsimp [gatewayMarginalSum]
  exact ⟨hb.2.2, hb.2.1⟩

theorem gatewayMarginalSum_bounds
    (R M d : Nat) (hM0 : 0 < M) (hMR : M ≤ R) :
    (M : ℝ) * (d : ℝ) / (R : ℝ) ≤ gatewayMarginalSum R M d ∧
      gatewayMarginalSum R M d ≤
        (M : ℝ) * (d : ℝ) / ((R - M + 1 : Nat) : ℝ) := by
  have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (hM0.trans_le hMR)
  have hlower : ∀ j ∈ Finset.range M,
      (d : ℝ) / (R : ℝ) ≤ (d : ℝ) / ((R - j : Nat) : ℝ) := by
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    have hden0 : (0 : ℝ) < ((R - j : Nat) : ℝ) := by
      exact_mod_cast (by omega : 0 < R - j)
    apply (div_le_div_iff₀ hR0 hden0).2
    have hcast : (((R - j : Nat) : ℝ)) ≤ (R : ℝ) := by
      exact_mod_cast Nat.sub_le R j
    exact mul_le_mul_of_nonneg_left hcast (Nat.cast_nonneg d)
  have hupper : ∀ j ∈ Finset.range M,
      (d : ℝ) / ((R - j : Nat) : ℝ) ≤
        (d : ℝ) / ((R - M + 1 : Nat) : ℝ) := by
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    have hleft0 : (0 : ℝ) < ((R - j : Nat) : ℝ) := by
      exact_mod_cast (by omega : 0 < R - j)
    have hright0 : (0 : ℝ) < ((R - M + 1 : Nat) : ℝ) := by positivity
    apply (div_le_div_iff₀ hleft0 hright0).2
    have hcast : (((R - M + 1 : Nat) : ℝ)) ≤ ((R - j : Nat) : ℝ) := by
      exact_mod_cast (by omega : R - M + 1 ≤ R - j)
    exact mul_le_mul_of_nonneg_left hcast (Nat.cast_nonneg d)
  constructor
  · have hs := Finset.sum_le_sum hlower
    calc
      (M : ℝ) * (d : ℝ) / (R : ℝ) =
          (M : ℝ) * ((d : ℝ) / (R : ℝ)) := by ring
      _ ≤ gatewayMarginalSum R M d := by
        simpa [gatewayMarginalSum] using hs
  · have hs := Finset.sum_le_sum hupper
    calc
      gatewayMarginalSum R M d ≤
          (M : ℝ) * ((d : ℝ) / ((R - M + 1 : Nat) : ℝ)) := by
        simpa [gatewayMarginalSum] using hs
      _ = (M : ℝ) * (d : ℝ) / ((R - M + 1 : Nat) : ℝ) := by ring

theorem hypergeometricGatewayHit_lowDegree_envelope
    (R M d : Nat) (hM0 : 0 < M) (h : d + M ≤ R) :
    (M : ℝ) * (d : ℝ) / (R : ℝ) -
          ((M : ℝ) * (d : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 ≤
        1 - hypergeometricGatewayMiss R M d ∧
      1 - hypergeometricGatewayMiss R M d ≤
        (M : ℝ) * (d : ℝ) / ((R - M + 1 : Nat) : ℝ) := by
  have hMR : M ≤ R := by omega
  have hbon := hypergeometricGatewayHit_lowDegree_bounds R M d h
  dsimp only at hbon
  have hsum := gatewayMarginalSum_bounds R M d hM0 hMR
  have hS0 : 0 ≤ gatewayMarginalSum R M d := by
    dsimp [gatewayMarginalSum]
    positivity
  have hU0 : 0 ≤
      (M : ℝ) * (d : ℝ) / ((R - M + 1 : Nat) : ℝ) := by positivity
  have hsq : (gatewayMarginalSum R M d) ^ 2 ≤
      ((M : ℝ) * (d : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 :=
    (sq_le_sq₀ hS0 hU0).2 hsum.2
  constructor <;> nlinarith

theorem hypergeometricGatewayMiss_eq_zero_of_highDegree
    (R M d : Nat) (hMR : M ≤ R) (h : R < d + M) :
    hypergeometricGatewayMiss R M d = 0 := by
  dsimp [hypergeometricGatewayMiss]
  rw [Nat.choose_eq_zero_of_lt (by omega : R - M < d)]
  simp

theorem hypergeometricGatewayHit_envelope
    (R M d : Nat) (hM0 : 0 < M) (hMR : M ≤ R) (hdR : d < R) :
    (M : ℝ) * (d : ℝ) / (R : ℝ) -
          ((M : ℝ) * (d : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 ≤
        1 - hypergeometricGatewayMiss R M d ∧
      1 - hypergeometricGatewayMiss R M d ≤
        (M : ℝ) * (d : ℝ) / ((R - M + 1 : Nat) : ℝ) := by
  by_cases hlow : d + M ≤ R
  · exact hypergeometricGatewayHit_lowDegree_envelope R M d hM0 hlow
  · have hhigh : R < d + M := by omega
    have hzero := hypergeometricGatewayMiss_eq_zero_of_highDegree R M d hMR hhigh
    rw [hzero]
    have hL0 : (0 : ℝ) < ((R - M + 1 : Nat) : ℝ) := by positivity
    have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hM0.trans_le hMR
    have hdL : R - M + 1 ≤ d := by omega
    have hMd : R - M + 1 ≤ M * d := by
      exact hdL.trans (Nat.le_mul_of_pos_left d hM0)
    have ht1 : (1 : ℝ) ≤
        (M : ℝ) * (d : ℝ) / ((R - M + 1 : Nat) : ℝ) := by
      apply (le_div_iff₀ hL0).2
      norm_num only [one_mul]
      exact_mod_cast hMd
    have hLR : R - M + 1 ≤ R := by omega
    have hfrac : (d : ℝ) / (R : ℝ) ≤
        (d : ℝ) / ((R - M + 1 : Nat) : ℝ) := by
      apply (div_le_div_iff₀ hR0 hL0).2
      have hcast : (((R - M + 1 : Nat) : ℝ)) ≤ (R : ℝ) := by
        exact_mod_cast hLR
      exact mul_le_mul_of_nonneg_left hcast (Nat.cast_nonneg d)
    have hlin : (M : ℝ) * (d : ℝ) / (R : ℝ) ≤
        (M : ℝ) * (d : ℝ) / ((R - M + 1 : Nat) : ℝ) := by
      have hMnonneg : (0 : ℝ) ≤ (M : ℝ) := by positivity
      calc
        (M : ℝ) * (d : ℝ) / (R : ℝ) =
            (M : ℝ) * ((d : ℝ) / (R : ℝ)) := by ring
        _ ≤ (M : ℝ) * ((d : ℝ) / ((R - M + 1 : Nat) : ℝ)) :=
          mul_le_mul_of_nonneg_left hfrac hMnonneg
        _ = (M : ℝ) * (d : ℝ) / ((R - M + 1 : Nat) : ℝ) := by ring
    constructor <;> nlinarith [sq_nonneg
      ((M : ℝ) * (d : ℝ) / ((R - M + 1 : Nat) : ℝ))]

/-- The degree mass used in the finite model has exactly the capped Zipf
first moment already analyzed in `windowZipfMean`. -/
theorem cappedZipfDegreeFirstMoment_eq
    (a : ℝ) (R : Nat) (hR : 2 ≤ R) :
    (∑ d ∈ Finset.range R,
        cappedZipfDegreeMass a R d * (d : ℝ)) = windowZipfMean a R := by
  let f : Nat → ℝ := fun d => cappedZipfDegreeMass a R d * (d : ℝ)
  have hsplitLast : (∑ d ∈ Finset.range R, f d) =
      (∑ d ∈ Finset.range (R - 1), f d) + f (R - 1) := by
    calc
      (∑ d ∈ Finset.range R, f d) =
          ∑ d ∈ Finset.range ((R - 1) + 1), f d := by
            congr 2; omega
      _ = (∑ d ∈ Finset.range (R - 1), f d) + f (R - 1) := by
        rw [Finset.sum_range_succ]
  have hsplitFirst : (∑ d ∈ Finset.range (R - 1), f d) =
      f 0 + ∑ i ∈ Finset.range (R - 2), f (i + 1) := by
    calc
      (∑ d ∈ Finset.range (R - 1), f d) =
          ∑ d ∈ Finset.range ((R - 2) + 1), f d := by
            congr 2; omega
      _ = f 0 + ∑ i ∈ Finset.range (R - 2), f (i + 1) := by
        rw [Finset.sum_range_succ']
        ac_rfl
  change (∑ d ∈ Finset.range R, f d) = windowZipfMean a R
  rw [hsplitLast, hsplitFirst]
  dsimp only [f]
  have hinterm : ∀ i ∈ Finset.range (R - 2),
      cappedZipfDegreeMass a R (i + 1) * ((i + 1 : Nat) : ℝ) =
        (((i + 2 - 1 : Nat) : ℝ) * ((i + 2 : Nat) : ℝ) ^ (-a)) /
          zipfNormalizer a := by
    intro i hi
    have hiR : i + 2 < R := by
      have := Finset.mem_range.mp hi
      omega
    rw [cappedZipfDegreeMass, if_pos hiR]
    rw [show i + 1 + 1 = i + 2 by omega, show i + 2 - 1 = i + 1 by omega]
    have hcast : ((i + 1 : Nat) : ℝ) + 1 = ((i + 2 : Nat) : ℝ) := by
      exact_mod_cast (by omega : i + 1 + 1 = i + 2)
    rw [hcast]
    ring
  rw [Finset.sum_congr rfl hinterm]
  have hreindex :
      (∑ i ∈ Finset.range (R - 2),
        (((i + 2 - 1 : Nat) : ℝ) * ((i + 2 : Nat) : ℝ) ^ (-a)) /
          zipfNormalizer a) =
      ∑ k ∈ Finset.Ico 2 R,
        (((k - 1 : Nat) : ℝ) * (k : ℝ) ^ (-a)) / zipfNormalizer a := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show 2 + i = i + 2 by omega,
      show i + 2 - 1 = i + 1 by omega]
  rw [hreindex]
  simp only [Nat.cast_zero, mul_zero, zero_add]
  have hcap : cappedZipfDegreeMass a R (R - 1) =
      rpowTail a R / zipfNormalizer a := by
    rw [cappedZipfDegreeMass, if_neg (by omega : ¬(R - 1 + 1 < R)),
      if_pos (by omega : R - 1 + 1 = R)]
  rw [hcap]
  dsimp [windowZipfMean, windowDirectNumerator, cappedRpowTail]
  rw [Nat.cast_sub (by omega : 1 ≤ R)]
  rw [← Finset.sum_div]
  ring

theorem cappedZipfDegreeMass_sum_eq_one
    (a : ℝ) (R : Nat) (ha : 1 < a) (hR : 2 ≤ R) :
    (∑ d ∈ Finset.range R, cappedZipfDegreeMass a R d) = 1 := by
  let f : Nat → ℝ := fun d => cappedZipfDegreeMass a R d
  have hsplitLast : (∑ d ∈ Finset.range R, f d) =
      (∑ d ∈ Finset.range (R - 1), f d) + f (R - 1) := by
    calc
      (∑ d ∈ Finset.range R, f d) =
          ∑ d ∈ Finset.range ((R - 1) + 1), f d := by
            congr 2; omega
      _ = (∑ d ∈ Finset.range (R - 1), f d) + f (R - 1) := by
        rw [Finset.sum_range_succ]
  change (∑ d ∈ Finset.range R, f d) = 1
  rw [hsplitLast]
  dsimp only [f]
  have hinterm : ∀ i ∈ Finset.range (R - 1),
      cappedZipfDegreeMass a R i =
        ((i + 1 : Nat) : ℝ) ^ (-a) / zipfNormalizer a := by
    intro i hi
    have hiR : i + 1 < R := by
      have := Finset.mem_range.mp hi
      omega
    rw [cappedZipfDegreeMass, if_pos hiR]
    rw [Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_congr rfl hinterm]
  have hreindex :
      (∑ i ∈ Finset.range (R - 1),
        ((i + 1 : Nat) : ℝ) ^ (-a) / zipfNormalizer a) =
      ∑ k ∈ Finset.Ico 1 R, (k : ℝ) ^ (-a) / zipfNormalizer a := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [add_comm]
  rw [hreindex]
  have hcap : cappedZipfDegreeMass a R (R - 1) =
      rpowTail a R / zipfNormalizer a := by
    rw [cappedZipfDegreeMass, if_neg (by omega : ¬(R - 1 + 1 < R)),
      if_pos (by omega : R - 1 + 1 = R)]
  rw [hcap, ← Finset.sum_div]
  have hprefix : zipfPrefix a R =
      ∑ k ∈ Finset.Ico 1 R, (k : ℝ) ^ (-a) := by
    dsimp [zipfPrefix]
    rw [Finset.sum_Ico_eq_sum_range]
    calc
      (∑ k ∈ Finset.range R, (k : ℝ) ^ (-a)) =
          ∑ k ∈ Finset.range ((R - 1) + 1), (k : ℝ) ^ (-a) := by
            congr 2; omega
      _ = (0 : ℝ) ^ (-a) +
          ∑ i ∈ Finset.range (R - 1), ((i + 1 : Nat) : ℝ) ^ (-a) := by
        rw [Finset.sum_range_succ']
        norm_num only [Nat.cast_zero]
        ac_rfl
      _ = ∑ i ∈ Finset.range (R - 1),
          ((1 + i : Nat) : ℝ) ^ (-a) := by
        rw [Real.zero_rpow (by linarith : -a ≠ 0), zero_add]
        apply Finset.sum_congr rfl
        intro i hi
        rw [add_comm]
  have hz := zipfNormalizer_eq_prefix_add_tail ha R
  rw [hprefix] at hz
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  rw [← add_div, ← hz]
  exact div_self (ne_of_gt hzpos)

theorem cappedZipfDegreeMass_nonneg
    (a : ℝ) (R d : Nat) (hz : 0 < zipfNormalizer a) :
    0 ≤ cappedZipfDegreeMass a R d := by
  rw [cappedZipfDegreeMass]
  split_ifs
  · exact div_nonneg (Real.rpow_nonneg (by positivity) _) hz.le
  · exact div_nonneg (rpowTail_nonneg a R) hz.le
  · exact le_rfl

noncomputable def windowZipfSecondNumerator (a : ℝ) (R : Nat) : ℝ :=
  (∑ k ∈ Finset.Ico 2 R,
      (((k - 1 : Nat) : ℝ) ^ 2 * (k : ℝ) ^ (-a))) +
    (((R - 1 : Nat) : ℝ) ^ 2 * rpowTail a R)

noncomputable def windowZipfSecondMoment (a : ℝ) (R : Nat) : ℝ :=
  windowZipfSecondNumerator a R / zipfNormalizer a

theorem windowZipfSecondNumerator_nonneg (a : ℝ) (R : Nat) :
    0 ≤ windowZipfSecondNumerator a R := by
  dsimp [windowZipfSecondNumerator]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)
  · exact mul_nonneg (sq_nonneg _) (rpowTail_nonneg a R)

theorem cappedZipfDegreeSecondMoment_eq
    (a : ℝ) (R : Nat) (hR : 2 ≤ R) :
    (∑ d ∈ Finset.range R,
        cappedZipfDegreeMass a R d * (d : ℝ) ^ 2) =
      windowZipfSecondMoment a R := by
  let f : Nat → ℝ := fun d => cappedZipfDegreeMass a R d * (d : ℝ) ^ 2
  have hsplitLast : (∑ d ∈ Finset.range R, f d) =
      (∑ d ∈ Finset.range (R - 1), f d) + f (R - 1) := by
    calc
      (∑ d ∈ Finset.range R, f d) =
          ∑ d ∈ Finset.range ((R - 1) + 1), f d := by
            congr 2; omega
      _ = (∑ d ∈ Finset.range (R - 1), f d) + f (R - 1) := by
        rw [Finset.sum_range_succ]
  have hsplitFirst : (∑ d ∈ Finset.range (R - 1), f d) =
      f 0 + ∑ i ∈ Finset.range (R - 2), f (i + 1) := by
    calc
      (∑ d ∈ Finset.range (R - 1), f d) =
          ∑ d ∈ Finset.range ((R - 2) + 1), f d := by
            congr 2; omega
      _ = f 0 + ∑ i ∈ Finset.range (R - 2), f (i + 1) := by
        rw [Finset.sum_range_succ']
        ac_rfl
  change (∑ d ∈ Finset.range R, f d) = windowZipfSecondMoment a R
  rw [hsplitLast, hsplitFirst]
  dsimp only [f]
  have hinterm : ∀ i ∈ Finset.range (R - 2),
      cappedZipfDegreeMass a R (i + 1) * ((i + 1 : Nat) : ℝ) ^ 2 =
        (((i + 2 - 1 : Nat) : ℝ) ^ 2 * ((i + 2 : Nat) : ℝ) ^ (-a)) /
          zipfNormalizer a := by
    intro i hi
    have hiR : i + 2 < R := by
      have := Finset.mem_range.mp hi
      omega
    rw [cappedZipfDegreeMass, if_pos hiR]
    rw [show i + 1 + 1 = i + 2 by omega, show i + 2 - 1 = i + 1 by omega]
    have hcast : ((i + 1 : Nat) : ℝ) + 1 = ((i + 2 : Nat) : ℝ) := by
      exact_mod_cast (by omega : i + 1 + 1 = i + 2)
    rw [hcast]
    ring
  rw [Finset.sum_congr rfl hinterm]
  have hreindex :
      (∑ i ∈ Finset.range (R - 2),
        (((i + 2 - 1 : Nat) : ℝ) ^ 2 * ((i + 2 : Nat) : ℝ) ^ (-a)) /
          zipfNormalizer a) =
      ∑ k ∈ Finset.Ico 2 R,
        (((k - 1 : Nat) : ℝ) ^ 2 * (k : ℝ) ^ (-a)) /
          zipfNormalizer a := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show 2 + i = i + 2 by omega,
      show i + 2 - 1 = i + 1 by omega]
  rw [hreindex]
  simp only [Nat.cast_zero, zero_pow (by norm_num : (2 : Nat) ≠ 0), mul_zero,
    zero_add]
  have hcap : cappedZipfDegreeMass a R (R - 1) =
      rpowTail a R / zipfNormalizer a := by
    rw [cappedZipfDegreeMass, if_neg (by omega : ¬(R - 1 + 1 < R)),
      if_pos (by omega : R - 1 + 1 = R)]
  rw [hcap]
  dsimp [windowZipfSecondMoment, windowZipfSecondNumerator]
  rw [← Finset.sum_div]
  ring

theorem interiorSecondTerm_le_windowFactor
    (a C : ℝ) (n R k : Nat) (hC : 0 ≤ C)
    (ha : 2 - C / (n : ℝ) ≤ a) (hk : k ∈ Finset.Ico 2 R) :
    (((k - 1 : Nat) : ℝ) ^ 2 * (k : ℝ) ^ (-a)) ≤
      (R : ℝ) ^ (C / (n : ℝ)) := by
  have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
  have hkR : k ≤ R := (Finset.mem_Ico.mp hk).2.le
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hdle : (((k - 1 : Nat) : ℝ)) ≤ (k : ℝ) := by
    exact_mod_cast Nat.sub_le k 1
  have hsq : (((k - 1 : Nat) : ℝ)) ^ 2 ≤ (k : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hdle
  calc
    (((k - 1 : Nat) : ℝ) ^ 2 * (k : ℝ) ^ (-a)) ≤
        (k : ℝ) ^ 2 * (k : ℝ) ^ (-a) :=
      mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (by positivity) _)
    _ = (k : ℝ) ^ (2 - a) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add hkpos]
      congr 1
    _ ≤ (k : ℝ) ^ (C / (n : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hkone (by linarith)
    _ ≤ (R : ℝ) ^ (C / (n : ℝ)) := by
      apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkR)
      exact div_nonneg hC (Nat.cast_nonneg n)

theorem windowZipfSecondNumerator_le
    (a C : ℝ) (n R : Nat) (hC : 0 ≤ C) (ha1 : 1 < a)
    (ha : 2 - C / (n : ℝ) ≤ a) (hR : 2 ≤ R) :
    windowZipfSecondNumerator a R ≤
      (R : ℝ) * (R : ℝ) ^ (C / (n : ℝ)) +
        (R : ℝ) ^ 2 *
          ((R : ℝ) ^ (-a) + (R : ℝ) ^ (1 - a) / (a - 1)) := by
  have hfactor0 : 0 ≤ (R : ℝ) ^ (C / (n : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hinterior :
      (∑ k ∈ Finset.Ico 2 R,
        (((k - 1 : Nat) : ℝ) ^ 2 * (k : ℝ) ^ (-a))) ≤
        (R : ℝ) * (R : ℝ) ^ (C / (n : ℝ)) := by
    calc
      (∑ k ∈ Finset.Ico 2 R,
          (((k - 1 : Nat) : ℝ) ^ 2 * (k : ℝ) ^ (-a))) ≤
          ∑ k ∈ Finset.Ico 2 R, (R : ℝ) ^ (C / (n : ℝ)) := by
            apply Finset.sum_le_sum
            intro k hk
            exact interiorSecondTerm_le_windowFactor a C n R k hC ha hk
      _ = ((R - 2 : Nat) : ℝ) * (R : ℝ) ^ (C / (n : ℝ)) := by simp
      _ ≤ (R : ℝ) * (R : ℝ) ^ (C / (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hfactor0
        exact_mod_cast Nat.sub_le R 2
  have htail := rpowTail_le a ha1 R (by omega : 1 ≤ R)
  have hcapSq : (((R - 1 : Nat) : ℝ)) ^ 2 ≤ (R : ℝ) ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).2
    exact_mod_cast Nat.sub_le R 1
  have hcap : (((R - 1 : Nat) : ℝ)) ^ 2 * rpowTail a R ≤
      (R : ℝ) ^ 2 *
        ((R : ℝ) ^ (-a) + (R : ℝ) ^ (1 - a) / (a - 1)) := by
    calc
      (((R - 1 : Nat) : ℝ)) ^ 2 * rpowTail a R ≤
          (R : ℝ) ^ 2 * rpowTail a R :=
        mul_le_mul_of_nonneg_right hcapSq (rpowTail_nonneg a R)
      _ ≤ (R : ℝ) ^ 2 *
          ((R : ℝ) ^ (-a) + (R : ℝ) ^ (1 - a) / (a - 1)) :=
        mul_le_mul_of_nonneg_left htail (sq_nonneg (R : ℝ))
  dsimp [windowZipfSecondNumerator]
  exact add_le_add hinterior hcap

theorem windowZipfSecondNumerator_le_four_mul
    (a C : ℝ) (n R : Nat) (hC : 0 ≤ C) (ha32 : (3 / 2 : ℝ) ≤ a)
    (ha : 2 - C / (n : ℝ) ≤ a) (hR : 2 ≤ R) :
    windowZipfSecondNumerator a R ≤
      4 * (R : ℝ) * (R : ℝ) ^ (C / (n : ℝ)) := by
  have ha1 : 1 < a := by linarith
  have hbase : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
  have hRpos : (0 : ℝ) < (R : ℝ) := by positivity
  let F : ℝ := (R : ℝ) ^ (C / (n : ℝ))
  have hF0 : 0 ≤ F := Real.rpow_nonneg (by positivity) _
  have hgap : (R : ℝ) ^ (2 - a) ≤ F := by
    dsimp [F]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hden : 0 < a - 1 := by linarith
  have hinv : (1 : ℝ) / (a - 1) ≤ 2 := by
    apply (div_le_iff₀ hden).2
    linarith
  have heq1 : (R : ℝ) ^ 2 * (R : ℝ) ^ (-a) =
      (R : ℝ) ^ (2 - a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hRpos]
    congr 1
  have heq2 : (R : ℝ) ^ 2 *
      ((R : ℝ) ^ (1 - a) / (a - 1)) =
        (R : ℝ) * (R : ℝ) ^ (2 - a) / (a - 1) := by
    have hp : (R : ℝ) * (R : ℝ) ^ (1 - a) =
        (R : ℝ) ^ (2 - a) := by
      calc
        (R : ℝ) * (R : ℝ) ^ (1 - a) =
            (R : ℝ) ^ (1 : ℝ) * (R : ℝ) ^ (1 - a) := by
          rw [Real.rpow_one]
        _ = (R : ℝ) ^ ((1 : ℝ) + (1 - a)) :=
          (Real.rpow_add hRpos 1 (1 - a)).symm
        _ = (R : ℝ) ^ (2 - a) := by ring_nf
    calc
      (R : ℝ) ^ 2 * ((R : ℝ) ^ (1 - a) / (a - 1)) =
          (R : ℝ) * ((R : ℝ) * (R : ℝ) ^ (1 - a)) / (a - 1) := by
        rw [pow_two]
        ring
      _ = (R : ℝ) * (R : ℝ) ^ (2 - a) / (a - 1) := by rw [hp]
  have htailPart : (R : ℝ) ^ (2 - a) +
      (R : ℝ) * (R : ℝ) ^ (2 - a) / (a - 1) ≤
        3 * (R : ℝ) * F := by
    have hfirst : (R : ℝ) ^ (2 - a) ≤ (R : ℝ) * F := by
      calc
        (R : ℝ) ^ (2 - a) ≤ F := hgap
        _ ≤ (R : ℝ) * F := by nlinarith
    have hsecond : (R : ℝ) * (R : ℝ) ^ (2 - a) / (a - 1) ≤
        2 * (R : ℝ) * F := by
      calc
        (R : ℝ) * (R : ℝ) ^ (2 - a) / (a - 1) ≤
            (R : ℝ) * F / (a - 1) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hgap (by positivity)) hden.le
        _ = ((R : ℝ) * F) * (1 / (a - 1)) := by ring
        _ ≤ ((R : ℝ) * F) * 2 :=
          mul_le_mul_of_nonneg_left hinv (mul_nonneg (by positivity) hF0)
        _ = 2 * (R : ℝ) * F := by ring
    linarith
  have hnum := windowZipfSecondNumerator_le a C n R hC ha1 ha hR
  rw [mul_add, heq1, heq2] at hnum
  have htailPart' : (R : ℝ) ^ (2 - a) +
      (R : ℝ) * (R : ℝ) ^ (2 - a) / (a - 1) ≤
        3 * (R : ℝ) * (R : ℝ) ^ (C / (n : ℝ)) := by
    simpa only [F] using htailPart
  nlinarith

theorem sourceMoleculeCount_div_reactionCount_tendsto_zero :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ))
      atTop (𝓝 0) := by
  have hninv : Tendsto (fun n : Nat => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hratio := sourceReactionCount_div_nat_molecule_tendsto_one.inv₀ one_ne_zero
  have hprod : Tendsto (fun n : Nat =>
      (n : ℝ)⁻¹ *
        ((sourceReactionCount n : ℝ) /
          ((n : ℝ) * (sourceMoleculeCount n : ℝ)))⁻¹) atTop (𝓝 0) := by
    simpa only [zero_mul] using hninv.mul hratio
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hX : (sourceMoleculeCount n : ℝ) ≠ 0 := by
    have hxnat : 0 < sourceMoleculeCount n :=
      (pow_pos (by norm_num) n).trans_le (sourceMoleculeCount_bounds hn).1
    exact_mod_cast (Nat.ne_of_gt hxnat)
  have hR : (sourceReactionCount n : ℝ) ≠ 0 := by
    rw [sourceReactionCount]
    positivity
  field_simp [hn0, hX, hR]

theorem calibratedSecondMoment_scaled_tendsto_zero
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        windowZipfSecondMoment (calibrationExponent lam hlam n)
          (sourceReactionCount n) /
        (sourceReactionCount n : ℝ) ^ 2) atTop (𝓝 0) := by
  let C : ℝ :=
    |criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))| + 1
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hfactor : Tendsto (fun n : Nat =>
      (sourceReactionCount n : ℝ) ^ (C / (n : ℝ))) atTop
      (𝓝 ((2 : ℝ) ^ C)) := by
    simpa only [neg_neg] using sourceReactionCount_rpow_window (-C)
  have hden : Tendsto (fun n : Nat =>
      zipfNormalizer (calibrationExponent lam hlam n)) atTop
      (𝓝 (Real.pi ^ 2 / 6)) := by
    have h := (continuousAt_zipfNormalizer one_lt_two).tendsto.comp
      (calibrationExponent_tendsto_two lam hlam)
    simpa only [zipfNormalizer_two] using h
  have hzeta : Real.pi ^ 2 / 6 ≠ 0 := by positivity
  let U : Nat → ℝ := fun n =>
    ((sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ)) *
      (4 * (sourceReactionCount n : ℝ) ^ (C / (n : ℝ)) /
        zipfNormalizer (calibrationExponent lam hlam n))
  have hbounded : Tendsto (fun n : Nat =>
      4 * (sourceReactionCount n : ℝ) ^ (C / (n : ℝ)) /
        zipfNormalizer (calibrationExponent lam hlam n)) atTop
      (𝓝 (4 * (2 : ℝ) ^ C / (Real.pi ^ 2 / 6))) := by
    exact (tendsto_const_nhds.mul hfactor).div hden hzeta
  have hU : Tendsto U atTop (𝓝 0) := by
    have h := sourceMoleculeCount_div_reactionCount_tendsto_zero.mul hbounded
    simpa only [zero_mul, U] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0)) hU
  · have hdenpos : ∀ᶠ n : Nat in atTop,
        0 < zipfNormalizer (calibrationExponent lam hlam n) :=
      hden (Ioi_mem_nhds (by positivity : 0 < Real.pi ^ 2 / 6))
    filter_upwards [hdenpos] with n hzp
    have hmom : 0 ≤ windowZipfSecondMoment (calibrationExponent lam hlam n)
        (sourceReactionCount n) := by
      dsimp [windowZipfSecondMoment]
      exact div_nonneg (windowZipfSecondNumerator_nonneg _ _) hzp.le
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hmom) (sq_nonneg _)
  · have ha32 : ∀ᶠ n : Nat in atTop,
        (3 / 2 : ℝ) ≤ calibrationExponent lam hlam n :=
      (calibrationExponent_tendsto_two lam hlam)
        (Ici_mem_nhds (by norm_num : (3 / 2 : ℝ) < 2))
    have hdenpos : ∀ᶠ n : Nat in atTop,
        0 < zipfNormalizer (calibrationExponent lam hlam n) :=
      hden (Ioi_mem_nhds (by positivity : 0 < Real.pi ^ 2 / 6))
    filter_upwards [eventually_ge_atTop 4, ha32, hdenpos] with n hn haN hzp
    have hRnat : 2 ≤ sourceReactionCount n := by
      have hp : 2 ≤ 2 ^ n := by
        have ht := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ n)
        norm_num at ht ⊢
        exact ht
      exact hp.trans (sourceReactionCount_bounds hn).1
    have hB := calibrationB_abs_le lam hlam n
    have hBlower : -C ≤ calibrationB lam hlam n := by
      dsimp [C]
      exact (neg_le_of_abs_le hB)
    have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
    have haLower : 2 - C / (n : ℝ) ≤ calibrationExponent lam hlam n := by
      have := div_le_div_of_nonneg_right hBlower hn0.le
      calc
        2 - C / (n : ℝ) = 2 + (-C) / (n : ℝ) := by ring
        _ ≤ 2 + calibrationB lam hlam n / (n : ℝ) := by linarith
        _ = calibrationExponent lam hlam n := by rfl
    have hnum := windowZipfSecondNumerator_le_four_mul
      (calibrationExponent lam hlam n) C n (sourceReactionCount n)
      hC0 haN haLower hRnat
    have hmoment :
        windowZipfSecondMoment (calibrationExponent lam hlam n)
            (sourceReactionCount n) ≤
          4 * (sourceReactionCount n : ℝ) *
              (sourceReactionCount n : ℝ) ^ (C / (n : ℝ)) /
            zipfNormalizer (calibrationExponent lam hlam n) := by
      dsimp [windowZipfSecondMoment]
      exact div_le_div_of_nonneg_right hnum hzp.le
    have hR0 : (sourceReactionCount n : ℝ) ≠ 0 := by positivity
    have hX0 : 0 ≤ (sourceMoleculeCount n : ℝ) := by positivity
    have hmul :
        (sourceMoleculeCount n : ℝ) *
            windowZipfSecondMoment (calibrationExponent lam hlam n)
              (sourceReactionCount n) ≤
          (sourceMoleculeCount n : ℝ) *
            (4 * (sourceReactionCount n : ℝ) *
                (sourceReactionCount n : ℝ) ^ (C / (n : ℝ)) /
              zipfNormalizer (calibrationExponent lam hlam n)) :=
      mul_le_mul_of_nonneg_left hmoment hX0
    have hscale := div_le_div_of_nonneg_right hmul
      (sq_nonneg (sourceReactionCount n : ℝ))
    calc
      (sourceMoleculeCount n : ℝ) *
            windowZipfSecondMoment (calibrationExponent lam hlam n)
              (sourceReactionCount n) /
          (sourceReactionCount n : ℝ) ^ 2 ≤
        (sourceMoleculeCount n : ℝ) *
            (4 * (sourceReactionCount n : ℝ) *
                (sourceReactionCount n : ℝ) ^ (C / (n : ℝ)) /
              zipfNormalizer (calibrationExponent lam hlam n)) /
          (sourceReactionCount n : ℝ) ^ 2 := hscale
      _ = U n := by
        dsimp [U]
        field_simp [hR0]

theorem calibratedFirstMoment_scaled_tendsto
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        windowZipfMean (calibrationExponent lam hlam n)
          (sourceReactionCount n) /
        (sourceReactionCount n : ℝ)) atTop (𝓝 lam) := by
  have hratio := sourceReactionCount_div_nat_molecule_tendsto_one.inv₀ one_ne_zero
  have htarget := (tendsto_const_nhds : Tendsto (fun _ : Nat => lam) atTop
    (𝓝 lam)).mul hratio
  have htarget' : Tendsto (fun n : Nat => lam *
      ((sourceReactionCount n : ℝ) /
        ((n : ℝ) * (sourceMoleculeCount n : ℝ)))⁻¹) atTop (𝓝 lam) := by
    simpa only [inv_one, mul_one] using htarget
  apply htarget'.congr'
  filter_upwards [eventually_ge_atTop 1,
    eventually_calibrationExponent_exact lam hlam] with n hn hexact
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hR : (sourceReactionCount n : ℝ) ≠ 0 := by
    rw [sourceReactionCount]
    positivity
  have hX : (sourceMoleculeCount n : ℝ) ≠ 0 := by
    have hxnat : 0 < sourceMoleculeCount n :=
      (pow_pos (by norm_num) n).trans_le (sourceMoleculeCount_bounds hn).1
    exact_mod_cast (Nat.ne_of_gt hxnat)
  field_simp [hn0, hR, hX] at hexact ⊢
  nlinarith

theorem sourceReactionCount_div_gatewayDenominator_tendsto_one
    (M : Nat) (hM0 : 0 < M) :
    Tendsto (fun n : Nat =>
      (sourceReactionCount n : ℝ) /
        ((sourceReactionCount n - M + 1 : Nat) : ℝ)) atTop (𝓝 1) := by
  have hRtop : Tendsto (fun n : Nat => (sourceReactionCount n : ℝ))
      atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp sourceReactionCount_tendsto_atTop
  have hsmall : Tendsto (fun n : Nat =>
      ((M - 1 : Nat) : ℝ) / (sourceReactionCount n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hRtop
  have hden : Tendsto (fun n : Nat =>
      1 - ((M - 1 : Nat) : ℝ) / (sourceReactionCount n : ℝ)) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).sub hsmall
  have hinv := hden.inv₀ one_ne_zero
  have hinv' : Tendsto (fun n : Nat =>
      (1 - ((M - 1 : Nat) : ℝ) / (sourceReactionCount n : ℝ))⁻¹)
      atTop (𝓝 1) := by
    simpa only [inv_one] using hinv
  apply hinv'.congr'
  filter_upwards [sourceReactionCount_tendsto_atTop.eventually
    (eventually_ge_atTop (M + 1))] with n hR
  have hR0 : (sourceReactionCount n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by omega : 0 < sourceReactionCount n)
  have hL0 : (((sourceReactionCount n - M + 1 : Nat) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by omega : 0 < sourceReactionCount n - M + 1)
  rw [Nat.cast_add, Nat.cast_sub (by omega : M ≤ sourceReactionCount n),
    Nat.cast_sub (by omega : 1 ≤ M)]
  field_simp [hR0, hL0]
  ring

/-- The exact one-molecule gateway-miss expectation under capped Zipf degree. -/
noncomputable def powerLawMoleculeGatewayMiss (a : ℝ) (R M : Nat) : ℝ :=
  ∑ d ∈ Finset.range R,
    cappedZipfDegreeMass a R d * hypergeometricGatewayMiss R M d

noncomputable def powerLawMoleculeGatewayHit (a : ℝ) (R M : Nat) : ℝ :=
  1 - powerLawMoleculeGatewayMiss a R M

theorem powerLawMoleculeGatewayHit_eq_sum
    (a : ℝ) (R M : Nat) (ha : 1 < a) (hR : 2 ≤ R) :
    powerLawMoleculeGatewayHit a R M =
      ∑ d ∈ Finset.range R,
        cappedZipfDegreeMass a R d *
          (1 - hypergeometricGatewayMiss R M d) := by
  have hmass := cappedZipfDegreeMass_sum_eq_one a R ha hR
  calc
    powerLawMoleculeGatewayHit a R M =
        1 - powerLawMoleculeGatewayMiss a R M := rfl
    _ = (∑ d ∈ Finset.range R, cappedZipfDegreeMass a R d) -
        powerLawMoleculeGatewayMiss a R M := by
      exact congrArg (fun x : ℝ => x - powerLawMoleculeGatewayMiss a R M) hmass.symm
    _ = (∑ d ∈ Finset.range R, cappedZipfDegreeMass a R d) -
        ∑ d ∈ Finset.range R,
          cappedZipfDegreeMass a R d * hypergeometricGatewayMiss R M d := rfl
    _ = ∑ d ∈ Finset.range R,
        (cappedZipfDegreeMass a R d -
          cappedZipfDegreeMass a R d * hypergeometricGatewayMiss R M d) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ d ∈ Finset.range R,
        cappedZipfDegreeMass a R d *
          (1 - hypergeometricGatewayMiss R M d) := by
      apply Finset.sum_congr rfl
      intro d hd
      ring

theorem powerLawMoleculeGatewayHit_bounds
    (a : ℝ) (R M : Nat) (ha : 1 < a) (hR : 2 ≤ R)
    (hM0 : 0 < M) (hMR : M ≤ R) :
    (M : ℝ) * windowZipfMean a R / (R : ℝ) -
          ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 *
            windowZipfSecondMoment a R ≤
        powerLawMoleculeGatewayHit a R M ∧
      powerLawMoleculeGatewayHit a R M ≤
        (M : ℝ) * windowZipfMean a R /
          ((R - M + 1 : Nat) : ℝ) := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  have hpoint : ∀ d ∈ Finset.range R,
      let mass := cappedZipfDegreeMass a R d
      mass * ((M : ℝ) * (d : ℝ) / (R : ℝ) -
          ((M : ℝ) * (d : ℝ) /
            ((R - M + 1 : Nat) : ℝ)) ^ 2) ≤
        mass * (1 - hypergeometricGatewayMiss R M d) ∧
      mass * (1 - hypergeometricGatewayMiss R M d) ≤
        mass * ((M : ℝ) * (d : ℝ) /
          ((R - M + 1 : Nat) : ℝ)) := by
    intro d hd
    have hdR := Finset.mem_range.mp hd
    have henv := hypergeometricGatewayHit_envelope R M d hM0 hMR hdR
    have hm0 := cappedZipfDegreeMass_nonneg a R d hzpos
    exact ⟨mul_le_mul_of_nonneg_left henv.1 hm0,
      mul_le_mul_of_nonneg_left henv.2 hm0⟩
  have hlowSum := Finset.sum_le_sum (fun d hd => (hpoint d hd).1)
  have huppSum := Finset.sum_le_sum (fun d hd => (hpoint d hd).2)
  have hfirst := cappedZipfDegreeFirstMoment_eq a R hR
  have hsecond := cappedZipfDegreeSecondMoment_eq a R hR
  have hlowEq :
      (∑ d ∈ Finset.range R,
        cappedZipfDegreeMass a R d *
          ((M : ℝ) * (d : ℝ) / (R : ℝ) -
            ((M : ℝ) * (d : ℝ) /
              ((R - M + 1 : Nat) : ℝ)) ^ 2)) =
        (M : ℝ) * windowZipfMean a R / (R : ℝ) -
          ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 *
            windowZipfSecondMoment a R := by
    calc
      (∑ d ∈ Finset.range R,
        cappedZipfDegreeMass a R d *
          ((M : ℝ) * (d : ℝ) / (R : ℝ) -
            ((M : ℝ) * (d : ℝ) /
              ((R - M + 1 : Nat) : ℝ)) ^ 2)) =
          ∑ d ∈ Finset.range R,
            (((M : ℝ) / (R : ℝ)) *
                (cappedZipfDegreeMass a R d * (d : ℝ)) -
              ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 *
                (cappedZipfDegreeMass a R d * (d : ℝ) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ = ((M : ℝ) / (R : ℝ)) *
            (∑ d ∈ Finset.range R,
              cappedZipfDegreeMass a R d * (d : ℝ)) -
          ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 *
            (∑ d ∈ Finset.range R,
              cappedZipfDegreeMass a R d * (d : ℝ) ^ 2) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = (M : ℝ) * windowZipfMean a R / (R : ℝ) -
          ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 *
            windowZipfSecondMoment a R := by
        rw [hfirst, hsecond]
        ring
  have huppEq :
      (∑ d ∈ Finset.range R,
        cappedZipfDegreeMass a R d *
          ((M : ℝ) * (d : ℝ) /
            ((R - M + 1 : Nat) : ℝ))) =
        (M : ℝ) * windowZipfMean a R /
          ((R - M + 1 : Nat) : ℝ) := by
    calc
      (∑ d ∈ Finset.range R,
        cappedZipfDegreeMass a R d *
          ((M : ℝ) * (d : ℝ) /
            ((R - M + 1 : Nat) : ℝ))) =
          ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) *
            (∑ d ∈ Finset.range R,
              cappedZipfDegreeMass a R d * (d : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ = (M : ℝ) * windowZipfMean a R /
          ((R - M + 1 : Nat) : ℝ) := by rw [hfirst]; ring
  rw [powerLawMoleculeGatewayHit_eq_sum a R M ha hR]
  rw [hlowEq] at hlowSum
  rw [huppEq] at huppSum
  exact ⟨hlowSum, huppSum⟩

theorem calibratedGatewayUpper_scaled_tendsto
    (lam : ℝ) (hlam : 0 < lam) (M : Nat) (hM0 : 0 < M) :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        ((M : ℝ) * windowZipfMean (calibrationExponent lam hlam n)
          (sourceReactionCount n) /
            ((sourceReactionCount n - M + 1 : Nat) : ℝ)))
      atTop (𝓝 ((M : ℝ) * lam)) := by
  have hA := calibratedFirstMoment_scaled_tendsto lam hlam
  have hq := sourceReactionCount_div_gatewayDenominator_tendsto_one M hM0
  have htarget :=
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => (M : ℝ)) atTop
      (𝓝 (M : ℝ))).mul hA).mul hq
  have htarget' : Tendsto (fun n : Nat =>
      ((M : ℝ) * ((sourceMoleculeCount n : ℝ) *
        windowZipfMean (calibrationExponent lam hlam n)
          (sourceReactionCount n) / (sourceReactionCount n : ℝ))) *
        ((sourceReactionCount n : ℝ) /
          ((sourceReactionCount n - M + 1 : Nat) : ℝ)))
      atTop (𝓝 ((M : ℝ) * lam)) := by
    simpa only [mul_one] using htarget
  apply htarget'.congr'
  filter_upwards [sourceReactionCount_tendsto_atTop.eventually
    (eventually_ge_atTop (M + 1))] with n hR
  have hR0 : (sourceReactionCount n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by omega : 0 < sourceReactionCount n)
  have hL0 : (((sourceReactionCount n - M + 1 : Nat) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by omega : 0 < sourceReactionCount n - M + 1)
  field_simp [hR0, hL0]

theorem calibratedGatewayQuadraticError_scaled_tendsto_zero
    (lam : ℝ) (hlam : 0 < lam) (M : Nat) (hM0 : 0 < M) :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        (((M : ℝ) / ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 *
          windowZipfSecondMoment (calibrationExponent lam hlam n)
            (sourceReactionCount n))) atTop (𝓝 0) := by
  have hq := sourceReactionCount_div_gatewayDenominator_tendsto_one M hM0
  have hE := calibratedSecondMoment_scaled_tendsto_zero lam hlam
  have htarget :=
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => ((M : ℝ) ^ 2)) atTop
      (𝓝 ((M : ℝ) ^ 2))).mul (hq.pow 2)).mul hE
  have htarget' : Tendsto (fun n : Nat =>
      (((M : ℝ) ^ 2) *
        ((sourceReactionCount n : ℝ) /
          ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2) *
        ((sourceMoleculeCount n : ℝ) *
          windowZipfSecondMoment (calibrationExponent lam hlam n)
            (sourceReactionCount n) / (sourceReactionCount n : ℝ) ^ 2))
      atTop (𝓝 0) := by
    simpa only [one_pow, mul_one, mul_zero] using htarget
  apply htarget'.congr'
  filter_upwards [sourceReactionCount_tendsto_atTop.eventually
    (eventually_ge_atTop (M + 1))] with n hR
  have hR0 : (sourceReactionCount n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by omega : 0 < sourceReactionCount n)
  have hL0 : (((sourceReactionCount n - M + 1 : Nat) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by omega : 0 < sourceReactionCount n - M + 1)
  field_simp [hR0, hL0]

theorem calibratedPowerLawMoleculeGatewayHit_scaled
    (lam : ℝ) (hlam : 0 < lam) (M : Nat) (hM0 : 0 < M) :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        powerLawMoleculeGatewayHit (calibrationExponent lam hlam n)
          (sourceReactionCount n) M) atTop (𝓝 ((M : ℝ) * lam)) := by
  have hA := calibratedFirstMoment_scaled_tendsto lam hlam
  have hmain0 :=
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (M : ℝ)) atTop
      (𝓝 (M : ℝ))).mul hA
  have hmain : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        ((M : ℝ) * windowZipfMean (calibrationExponent lam hlam n)
          (sourceReactionCount n) / (sourceReactionCount n : ℝ)))
      atTop (𝓝 ((M : ℝ) * lam)) := by
    apply hmain0.congr'
    exact Filter.Eventually.of_forall (fun n => by ring)
  have herr := calibratedGatewayQuadraticError_scaled_tendsto_zero lam hlam M hM0
  have hlower0 := hmain.sub herr
  have hlower : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        ((M : ℝ) * windowZipfMean (calibrationExponent lam hlam n)
            (sourceReactionCount n) / (sourceReactionCount n : ℝ) -
          ((M : ℝ) /
            ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 *
            windowZipfSecondMoment (calibrationExponent lam hlam n)
              (sourceReactionCount n)))
      atTop (𝓝 ((M : ℝ) * lam)) := by
    have hlower1 : Tendsto (fun n : Nat =>
        (sourceMoleculeCount n : ℝ) *
            ((M : ℝ) * windowZipfMean (calibrationExponent lam hlam n)
              (sourceReactionCount n) / (sourceReactionCount n : ℝ)) -
          (sourceMoleculeCount n : ℝ) *
            (((M : ℝ) /
              ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 *
              windowZipfSecondMoment (calibrationExponent lam hlam n)
                (sourceReactionCount n)))
        atTop (𝓝 ((M : ℝ) * lam)) := by
      simpa only [sub_zero] using hlower0
    apply hlower1.congr'
    exact Filter.Eventually.of_forall (fun n => by ring)
  have hupper := calibratedGatewayUpper_scaled_tendsto lam hlam M hM0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · have ha : ∀ᶠ n : Nat in atTop, 1 < calibrationExponent lam hlam n :=
      (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
    filter_upwards [ha, sourceReactionCount_tendsto_atTop.eventually
      (eventually_ge_atTop (max 2 M))] with n han hR
    have hb := powerLawMoleculeGatewayHit_bounds
      (calibrationExponent lam hlam n) (sourceReactionCount n) M han
      (by omega) hM0 (by omega)
    exact mul_le_mul_of_nonneg_left hb.1 (Nat.cast_nonneg _)
  · have ha : ∀ᶠ n : Nat in atTop, 1 < calibrationExponent lam hlam n :=
      (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
    filter_upwards [ha, sourceReactionCount_tendsto_atTop.eventually
      (eventually_ge_atTop (max 2 M))] with n han hR
    have hb := powerLawMoleculeGatewayHit_bounds
      (calibrationExponent lam hlam n) (sourceReactionCount n) M han
      (by omega) hM0 (by omega)
    exact mul_le_mul_of_nonneg_left hb.2 (Nat.cast_nonneg _)

/-- Exact seed-closed probability for independent molecule degree/subset draws. -/
noncomputable def powerLawSeedClosedProbability
    (a : ℝ) (R M X : Nat) : ℝ :=
  (powerLawMoleculeGatewayMiss a R M) ^ X

theorem powerLawSeedClosedProbability_exact (a : ℝ) (R M X : Nat) :
    powerLawSeedClosedProbability a R M X =
      (∑ d ∈ Finset.range R,
        cappedZipfDegreeMass a R d *
          ((Nat.choose (R - M) d : ℝ) / Nat.choose R d)) ^ X := by
  rfl

/-- Under exact mean-linear calibration, any fixed positive set of `M`
gateway reactions remains entirely uncatalyzed with limit `exp (-M * lambda)`. -/
theorem calibratedPowerLawSeedClosed
    (lam : ℝ) (hlam : 0 < lam) (M : Nat) (hM0 : 0 < M) :
    Tendsto (fun n : Nat => powerLawSeedClosedProbability
      (calibrationExponent lam hlam n) (sourceReactionCount n) M
        (sourceMoleculeCount n)) atTop
      (𝓝 (Real.exp (-((M : ℝ) * lam)))) := by
  let p : Nat → ℝ := fun n =>
    powerLawMoleculeGatewayHit (calibrationExponent lam hlam n)
      (sourceReactionCount n) M
  have hNp : Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ) * p n)
      atTop (𝓝 ((M : ℝ) * lam)) := by
    simpa only [p] using calibratedPowerLawMoleculeGatewayHit_scaled lam hlam M hM0
  have hxreal : Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp sourceMoleculeCount_tendsto_atTop
  have hp : Tendsto p atTop (𝓝 0) := by
    have h := hNp.mul hxreal.inv_tendsto_atTop
    have h' : Tendsto (fun n : Nat =>
        ((sourceMoleculeCount n : ℝ) * p n) *
          (sourceMoleculeCount n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using h
    apply h'.congr'
    filter_upwards [sourceMoleculeCount_tendsto_atTop.eventually
      (eventually_gt_atTop 0)] with n hxn
    field_simp
  have htheta : 0 < (M : ℝ) * lam :=
    mul_pos (by exact_mod_cast hM0) hlam
  have hprodpos : ∀ᶠ n : Nat in atTop,
      0 < (sourceMoleculeCount n : ℝ) * p n :=
    hNp (Ioi_mem_nhds htheta)
  have hpne : ∀ᶠ n : Nat in atTop, p n ≠ 0 := by
    filter_upwards [hprodpos] with n hn hzero
    rw [hzero, mul_zero] at hn
    exact (lt_irrefl 0 hn)
  have hplt : ∀ᶠ n : Nat in atTop, p n < 1 := hp (Iio_mem_nhds one_pos)
  simpa [powerLawSeedClosedProbability, p, powerLawMoleculeGatewayHit] using
    binomialNoHit_tendsto_exp_neg sourceMoleculeCount p ((M : ℝ) * lam)
      hp hpne hplt hNp

/-- For one specified gateway, averaging the conditional hit probability is
exactly the capped mean divided by the reaction count. -/
noncomputable def oneGatewayHitProbability (a : ℝ) (R : Nat) : ℝ :=
  windowZipfMean a R / (R : ℝ)

noncomputable def oneGatewaySeedClosedProbability
    (a : ℝ) (R X : Nat) : ℝ :=
  (1 - oneGatewayHitProbability a R) ^ X

/-- Under exact mean-linear calibration, one fixed gateway remains closed with
limit `exp(-lambda)`. -/
theorem calibratedOneGatewaySeedClosed (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun n : Nat => oneGatewaySeedClosedProbability
      (calibrationExponent lam hlam n) (sourceReactionCount n)
      (sourceMoleculeCount n)) atTop (𝓝 (Real.exp (-lam))) := by
  let p : Nat → ℝ := fun n => oneGatewayHitProbability
    (calibrationExponent lam hlam n) (sourceReactionCount n)
  have hratio := sourceReactionCount_div_nat_molecule_tendsto_one.inv₀ one_ne_zero
  have hNp : Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ) * p n)
      atTop (𝓝 lam) := by
    have htarget := (tendsto_const_nhds : Tendsto (fun _ : Nat => lam) atTop
      (𝓝 lam)).mul hratio
    have htarget' : Tendsto (fun n : Nat => lam *
        ((sourceReactionCount n : ℝ) /
          ((n : ℝ) * (sourceMoleculeCount n : ℝ)))⁻¹) atTop (𝓝 lam) := by
      simpa only [inv_one, mul_one] using htarget
    apply htarget'.congr'
    filter_upwards [eventually_ge_atTop 1,
      eventually_calibrationExponent_exact lam hlam] with n hn hexact
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hR : (sourceReactionCount n : ℝ) ≠ 0 := by
      rw [sourceReactionCount]
      positivity
    have hX : (sourceMoleculeCount n : ℝ) ≠ 0 := by
      have hxnat : 0 < sourceMoleculeCount n :=
        (pow_pos (by norm_num) n).trans_le (sourceMoleculeCount_bounds hn).1
      exact_mod_cast (Nat.ne_of_gt hxnat)
    dsimp [p, oneGatewayHitProbability]
    field_simp [hn0, hR, hX] at hexact ⊢
    nlinarith
  have hxreal : Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp sourceMoleculeCount_tendsto_atTop
  have hp : Tendsto p atTop (𝓝 0) := by
    have h := hNp.mul hxreal.inv_tendsto_atTop
    have h' : Tendsto (fun n : Nat =>
        ((sourceMoleculeCount n : ℝ) * p n) *
          (sourceMoleculeCount n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using h
    apply h'.congr'
    filter_upwards [sourceMoleculeCount_tendsto_atTop.eventually
      (eventually_gt_atTop 0)] with n hxn
    field_simp
  have hpne : ∀ᶠ n : Nat in atTop, p n ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1,
      eventually_calibrationExponent_exact lam hlam] with n hn hexact
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hmean : windowZipfMean (calibrationExponent lam hlam n)
        (sourceReactionCount n) ≠ 0 := by
      intro hz
      rw [hz, zero_div] at hexact
      exact ne_of_gt hlam hexact.symm
    have hR : (sourceReactionCount n : ℝ) ≠ 0 := by
      rw [sourceReactionCount]
      positivity
    exact div_ne_zero hmean hR
  have hplt : ∀ᶠ n : Nat in atTop, p n < 1 := hp (Iio_mem_nhds one_pos)
  simpa [oneGatewaySeedClosedProbability, p] using
    binomialNoHit_tendsto_exp_neg sourceMoleculeCount p lam hp hpne hplt hNp

end PowerLawSmallRAF
