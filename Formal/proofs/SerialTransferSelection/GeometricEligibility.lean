import proofs.SerialTransferSelection.ManyCycleParameters

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem historyBudget_mul_left (a : ℝ) (d : ℕ → ℝ) (k j : ℕ) :
    historyBudget (fun i => a*d i) k j = a*historyBudget d k j := by
  induction k generalizing j with
  | zero => simp [historyBudget]
  | succ k ih => simp only [historyBudget,ih]; ring

theorem baseline_transfer_identity (M j : ℕ) (hM : 0 < M) :
    32/((1/50 : ℝ)^2*baselineFloor j*(M : ℝ)) =
      160000/(M : ℝ)*(800/49 : ℝ)^j := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  have hp : (49/800 : ℝ)^j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hi : (800/49 : ℝ)^j = ((49/800 : ℝ)^j)⁻¹ := by
    rw [← inv_pow]
    norm_num
  rw [hi]
  unfold baselineFloor
  field_simp [hm,hp]
  ring

theorem baseline_geometric_budget (N M JB JR K : ℕ) (hM : 0 < M) (qb qr t : ℝ) :
    historyBudget (fun j => sourceCycleError N M JB JR qb qr t (baselineFloor j) (1/50)) K 0 =
      (K : ℝ)*(chemicalCycleError N M t+t*qb/JB+(M : ℝ)*(5376*qr/JR))+
      160000/(M : ℝ)*historyBudget (fun j => (800/49 : ℝ)^j) K 0 := by
  simp_rw [sourceCycleError_chemical_split,baseline_transfer_identity M _ hM]
  rw [historyBudget_add,historyBudget_add,historyBudget_add,
    historyBudget_mul_left,historyBudget_const,historyBudget_const,historyBudget_const]
  ring

theorem exists_baseline_population (K : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℕ, 0 < B ∧
      160000/((2*B : ℕ) : ℝ)*historyBudget (fun j => (800/49 : ℝ)^j) K 0 < δ := by
  let A := 160000*historyBudget (fun j => (800/49 : ℝ)^j) K 0
  have hA : 0 ≤ A := mul_nonneg (by norm_num)
    (historyBudget_nonneg _ (fun _ => by positivity) K 0)
  obtain ⟨B,hB⟩ := exists_nat_gt (max (A/δ) 0)
  have hb : 0 < (B : ℝ) := lt_of_le_of_lt (le_max_right _ _) hB
  refine ⟨B,by exact_mod_cast hb,?_⟩
  have hbig : A/δ < B := lt_of_le_of_lt (le_max_left _ _) hB
  have ha : A < (B : ℝ)*δ := (div_lt_iff₀ hδ).mp hbig
  have hden : (0 : ℝ) < ((2*B : ℕ) : ℝ) := by push_cast; positivity
  have hh : A/((2*B : ℕ) : ℝ) < δ := (div_lt_iff₀ hden).mpr (by
    push_cast
    nlinarith)
  convert hh using 1
  dsimp [A]
  ring

end SerialTransferSelection
