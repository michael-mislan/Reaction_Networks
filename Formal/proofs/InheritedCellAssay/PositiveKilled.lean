import proofs.InheritedCellAssay.CountThresholdSource

namespace InheritedCellAssay.PositiveKilled
open FiniteCopy CompositionalMemory

/-- Live counts one through seven; index seven is the cemetery. -/
def next (n : Fin 8) (b : Bool) : Fin 8 :=
  if b then ⟨min (n.val+1) 7, by omega⟩ else 7

noncomputable def source (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    FiniteJumpModel (Fin 8) Bool where
  next := next
  rate n b := (if b then c else 1-c) * (n.val+1)
  nonneg n b := by split <;> positivity

/-- Backward probability of ending at live count three through seven. -/
noncomputable def value (c t : ℝ) (n : Fin 8) : ℝ :=
  if n.val = 0 then (1*c^2) * (Real.exp (-t))^1 * (1-Real.exp (-t))^2 + (1*c^3) * (Real.exp (-t))^1 * (1-Real.exp (-t))^3 + (1*c^4) * (Real.exp (-t))^1 * (1-Real.exp (-t))^4 + (1*c^5) * (Real.exp (-t))^1 * (1-Real.exp (-t))^5 + (1*c^6) * (Real.exp (-t))^1 * (1-Real.exp (-t))^6 else
  if n.val = 1 then (2*c^1) * (Real.exp (-t))^2 * (1-Real.exp (-t))^1 + (3*c^2) * (Real.exp (-t))^2 * (1-Real.exp (-t))^2 + (4*c^3) * (Real.exp (-t))^2 * (1-Real.exp (-t))^3 + (5*c^4) * (Real.exp (-t))^2 * (1-Real.exp (-t))^4 + (6*c^5) * (Real.exp (-t))^2 * (1-Real.exp (-t))^5 else
  if n.val = 2 then (1*c^0) * (Real.exp (-t))^3 * (1-Real.exp (-t))^0 + (3*c^1) * (Real.exp (-t))^3 * (1-Real.exp (-t))^1 + (6*c^2) * (Real.exp (-t))^3 * (1-Real.exp (-t))^2 + (10*c^3) * (Real.exp (-t))^3 * (1-Real.exp (-t))^3 + (15*c^4) * (Real.exp (-t))^3 * (1-Real.exp (-t))^4 else
  if n.val = 3 then (1*c^0) * (Real.exp (-t))^4 * (1-Real.exp (-t))^0 + (4*c^1) * (Real.exp (-t))^4 * (1-Real.exp (-t))^1 + (10*c^2) * (Real.exp (-t))^4 * (1-Real.exp (-t))^2 + (20*c^3) * (Real.exp (-t))^4 * (1-Real.exp (-t))^3 else
  if n.val = 4 then (1*c^0) * (Real.exp (-t))^5 * (1-Real.exp (-t))^0 + (5*c^1) * (Real.exp (-t))^5 * (1-Real.exp (-t))^1 + (15*c^2) * (Real.exp (-t))^5 * (1-Real.exp (-t))^2 else
  if n.val = 5 then (1*c^0) * (Real.exp (-t))^6 * (1-Real.exp (-t))^0 + (6*c^1) * (Real.exp (-t))^6 * (1-Real.exp (-t))^1 else
  if n.val = 6 then (1*c^0) * (Real.exp (-t))^7 * (1-Real.exp (-t))^0 else 0

private theorem backward_0 (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (t : ℝ) :
    HasDerivAt (fun s => value c s 0) ((source c hc hc1).generator (value c t) 0) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hh := he.const_sub 1
  have h7 : value c t 7 = 0 := by rfl
  simp [source, next, FiniteJumpModel.generator, h7]
  convert (((((((he.pow 1).const_mul (1*c^2)).mul (hh.pow 2)).add (((he.pow 1).const_mul (1*c^3)).mul (hh.pow 3))).add (((he.pow 1).const_mul (1*c^4)).mul (hh.pow 4))).add (((he.pow 1).const_mul (1*c^5)).mul (hh.pow 5))).add (((he.pow 1).const_mul (1*c^6)).mul (hh.pow 6))) using 1
  all_goals first
  | solve | rfl
  | solve | norm_num [value, Fin.isValue]; ring

private theorem backward_1 (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (t : ℝ) :
    HasDerivAt (fun s => value c s 1) ((source c hc hc1).generator (value c t) 1) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hh := he.const_sub 1
  have h7 : value c t 7 = 0 := by rfl
  simp [source, next, FiniteJumpModel.generator, h7]
  convert (((((((he.pow 2).const_mul (2*c^1)).mul (hh.pow 1)).add (((he.pow 2).const_mul (3*c^2)).mul (hh.pow 2))).add (((he.pow 2).const_mul (4*c^3)).mul (hh.pow 3))).add (((he.pow 2).const_mul (5*c^4)).mul (hh.pow 4))).add (((he.pow 2).const_mul (6*c^5)).mul (hh.pow 5))) using 1
  all_goals first
  | solve | rfl
  | solve | norm_num [value, Fin.isValue]; ring

private theorem backward_2 (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (t : ℝ) :
    HasDerivAt (fun s => value c s 2) ((source c hc hc1).generator (value c t) 2) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hh := he.const_sub 1
  have h7 : value c t 7 = 0 := by rfl
  simp [source, next, FiniteJumpModel.generator, h7]
  convert (((((((he.pow 3).const_mul (1*c^0)).mul (hh.pow 0)).add (((he.pow 3).const_mul (3*c^1)).mul (hh.pow 1))).add (((he.pow 3).const_mul (6*c^2)).mul (hh.pow 2))).add (((he.pow 3).const_mul (10*c^3)).mul (hh.pow 3))).add (((he.pow 3).const_mul (15*c^4)).mul (hh.pow 4))) using 1
  all_goals first
  | solve | rfl
  | solve | norm_num [value, Fin.isValue]; ring

private theorem backward_3 (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (t : ℝ) :
    HasDerivAt (fun s => value c s 3) ((source c hc hc1).generator (value c t) 3) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hh := he.const_sub 1
  have h7 : value c t 7 = 0 := by rfl
  simp [source, next, FiniteJumpModel.generator, h7]
  convert ((((((he.pow 4).const_mul (1*c^0)).mul (hh.pow 0)).add (((he.pow 4).const_mul (4*c^1)).mul (hh.pow 1))).add (((he.pow 4).const_mul (10*c^2)).mul (hh.pow 2))).add (((he.pow 4).const_mul (20*c^3)).mul (hh.pow 3))) using 1
  all_goals first
  | solve | rfl
  | solve | norm_num [value, Fin.isValue]; ring

private theorem backward_4 (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (t : ℝ) :
    HasDerivAt (fun s => value c s 4) ((source c hc hc1).generator (value c t) 4) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hh := he.const_sub 1
  have h7 : value c t 7 = 0 := by rfl
  simp [source, next, FiniteJumpModel.generator, h7]
  convert (((((he.pow 5).const_mul (1*c^0)).mul (hh.pow 0)).add (((he.pow 5).const_mul (5*c^1)).mul (hh.pow 1))).add (((he.pow 5).const_mul (15*c^2)).mul (hh.pow 2))) using 1
  all_goals first
  | solve | rfl
  | solve | norm_num [value, Fin.isValue]; ring

private theorem backward_5 (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (t : ℝ) :
    HasDerivAt (fun s => value c s 5) ((source c hc hc1).generator (value c t) 5) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hh := he.const_sub 1
  have h7 : value c t 7 = 0 := by rfl
  simp [source, next, FiniteJumpModel.generator, h7]
  convert ((((he.pow 6).const_mul (1*c^0)).mul (hh.pow 0)).add (((he.pow 6).const_mul (6*c^1)).mul (hh.pow 1))) using 1
  all_goals first
  | solve | rfl
  | solve | norm_num [value, Fin.isValue]; ring

private theorem backward_6 (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (t : ℝ) :
    HasDerivAt (fun s => value c s 6) ((source c hc hc1).generator (value c t) 6) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hh := he.const_sub 1
  have h7 : value c t 7 = 0 := by rfl
  simp [source, next, FiniteJumpModel.generator, h7]
  convert (((he.pow 7).const_mul (1*c^0)).mul (hh.pow 0)) using 1
  all_goals first
  | solve | rfl
  | solve | norm_num [value, Fin.isValue]; ring

theorem backward (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (t : ℝ) (n : Fin 8) :
    HasDerivAt (fun s => value c s n) ((source c hc hc1).generator (value c t) n) t := by
  fin_cases n
  · exact backward_0 c hc hc1 t
  · exact backward_1 c hc hc1 t
  · exact backward_2 c hc hc1 t
  · exact backward_3 c hc hc1 t
  · exact backward_4 c hc hc1 t
  · exact backward_5 c hc hc1 t
  · exact backward_6 c hc hc1 t
  · simpa [value, source, next, FiniteJumpModel.generator] using hasDerivAt_const t (0 : ℝ)

theorem finite_failure_exact (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    finiteTimeExpectation (source c hc hc1) CountThreshold.horizon
      (fun n : Fin 8 => if 2 ≤ n.val ∧ n.val ≤ 6 then 1 else 0) 0 =
      (1/2) * ((c/2)^2+(c/2)^3+(c/2)^4+(c/2)^5+(c/2)^6) := by
  have hv : (fun n : Fin 8 => if 2 ≤ n.val ∧ n.val ≤ 6 then (1 : ℝ) else 0) = value c 0 := by
    funext n
    fin_cases n <;> norm_num [value]
  rw [hv, CountThreshold.backward_solution_expectation _ _ (backward c hc hc1)]
  change value c (Real.log 2) 0 = _
  norm_num [value, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  ring

/-- A strict lower bound for the finite killed event, before trajectory transport. -/
theorem finite_failure_gt :
    (1/20 : ℝ) < (5/24) * finiteTimeExpectation
      (source (10000/10001) (by norm_num) (by norm_num)) CountThreshold.horizon
      (fun n : Fin 8 => if 2 ≤ n.val ∧ n.val ≤ 6 then 1 else 0) 0 := by
  rw [finite_failure_exact]
  norm_num

end InheritedCellAssay.PositiveKilled
