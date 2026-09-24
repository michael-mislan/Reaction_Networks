import proofs.FiniteCopyReactor.Residence

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

inductive SupplyKind | foodU | foodW | gross deriving DecidableEq, Fintype

def supplyRateCap : SupplyKind → ℝ
  | .foodU => 1
  | .foodW => 1
  | .gross => 9/200

def supplyMark (k : SupplyKind) : CompetitionChannel → ℝ
  | .inl j => match k with
      | .foodU => if j=10 then 1 else 0
      | .foodW => if j=11 then 1 else 0
      | .gross => 0
  | .inr _ => match k with
      | .foodU => 0
      | .foodW => 0
      | .gross => 1

theorem supply_mark_binary (k : SupplyKind) (j : CompetitionChannel) :
    supplyMark k j=0 ∨ supplyMark k j=1 := by
  cases j with
  | inl j =>
    cases k with
    | foodU => dsimp [supplyMark]; split_ifs <;> simp
    | foodW => dsimp [supplyMark]; split_ifs <;> simp
    | gross => simp [supplyMark]
  | inr j => cases k <;> simp [supplyMark]

theorem supply_rate_cap_nonneg (k : SupplyKind) : 0 ≤ supplyRateCap k := by cases k <;> norm_num [supplyRateCap]

theorem foodU_intensity (N : Counts) (V r d : ℝ) :
    (∑ j,competitionRate N V (1/500000000) (1/10) r d j*supplyMark .foodU j)=V := by
  simp [Fintype.sum_sum_type,competitionRate,supplyMark,countRate]

theorem foodW_intensity (N : Counts) (V r d : ℝ) :
    (∑ j,competitionRate N V (1/500000000) (1/10) r d j*supplyMark .foodW j)=V := by
  simp [Fintype.sum_sum_type,competitionRate,supplyMark,countRate]

theorem gross_intensity (N : Counts) (V r d : ℝ) :
    (∑ j,competitionRate N V (1/500000000) (1/10) r d j*supplyMark .gross j)=
      d*(N 2)+d/8000000000*(N 0)*(N 1)/V := by
  norm_num [Fintype.sum_sum_type,competitionRate,supplyMark,Fin.sum_univ_two,drivenRate_zero,drivenRate_one]
  ring

theorem supply_intensity_bound (k : SupplyKind) (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (_hd : 0 ≤ d) (hd' : d ≤ 1/25) (hc : resourceGood N V) :
    (∑ j,competitionRate N V (1/500000000) (1/10) r d j*supplyMark k j) ≤ supplyRateCap k*(V:ℝ) := by
  cases k with
  | foodU => rw [foodU_intensity]; simp [supplyRateCap]
  | foodW => rw [foodW_intensity]; simp [supplyRateCap]
  | gross =>
    rw [gross_intensity]
    have hp : (N 0:ℝ)*(N 1)/(V:ℝ) ≤ (121/100)*(V:ℝ) := by
      apply (div_le_iff₀ hV).mpr
      have hh := mul_le_mul (resource_count_cap N V hc 0) (resource_count_cap N V hc 1)
        (Nat.cast_nonneg (N 1)) (by positivity : (0:ℝ) ≤ (11/10)*V)
      nlinarith
    have hdp := mul_le_mul hd' hp (by positivity : 0 ≤ (N 0:ℝ)*(N 1)/(V:ℝ)) (by norm_num : (0:ℝ) ≤ 1/25)
    have hdx := mul_le_mul hd' (resource_count_cap N V hc 2) (Nat.cast_nonneg (N 2)) (by norm_num : (0:ℝ) ≤ 1/25)
    have he : d/8000000000*(N 0:ℝ)*(N 1)/(V:ℝ) = (d*((N 0:ℝ)*(N 1)/(V:ℝ)))/8000000000 := by ring
    rw [he]
    dsimp [supplyRateCap]
    nlinarith

end
end FiniteCopyReactor
