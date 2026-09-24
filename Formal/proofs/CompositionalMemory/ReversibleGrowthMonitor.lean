import proofs.CompositionalMemory.ReversibleRateBudget
import proofs.CompositionalMemory.ReversibleMonitoredDeadline

namespace CompositionalMemory
open FiniteCopy ControlledRows

noncomputable def reversibleReverseHazard (N : Nat) (ρ : ℝ) : CoupledFiniteState N → ℝ
  | none => 0
  | some ⟨j,_⟩ => if j.val=N then 0 else 2*ρ*((N : ℝ)+j.val)

theorem reversibleReverseHazard_nonneg (N : Nat) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (s : CoupledFiniteState N) : 0 ≤ reversibleReverseHazard N ρ s := by
  cases s with
  | none => rfl
  | some s => rcases s with ⟨j,a⟩; simp only [reversibleReverseHazard]; split_ifs <;> positivity

theorem reversibleReverseHazard_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (hρu : ρ ≤ 2/10000000)
    (s : CoupledFiniteState 53) : reversibleReverseHazard 53 ρ s ≤ 53/1250000 := by
  cases s with
  | none => norm_num [reversibleReverseHazard]
  | some s =>
    rcases s with ⟨j,a⟩
    have hj : (j.val : ℝ) ≤ 53 := by exact_mod_cast Nat.le_of_lt_succ j.isLt
    simp only [reversibleReverseHazard]
    split_ifs
    · norm_num
    · norm_num
      nlinarith [mul_nonneg hρ (sub_nonneg.mpr hj)]

noncomputable def reversibleMonitoredModel (N : Nat) (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) :=
  withExtraExit (reversibleFiniteModel N ε hε) none (reversibleReverseHazard N ρ)
    (reversibleReverseHazard_nonneg N ρ hρ)

theorem reversibleMonitored_total (ε ρ : ℝ) (hε : 0 ≤ ε) (hεu : ε ≤ 1/10)
    (hρ : 0 ≤ ρ) (hρu : ρ ≤ 2/10000000) (s : CoupledFiniteState 53) :
    (reversibleMonitoredModel 53 ε ρ hε hρ).total s ≤ 4000000 := by
  have hb := reversible_total_rate_cap 53 (by norm_num) ε hε hεu s
  have hk := reversibleReverseHazard_bound ρ hρ hρu s
  have he : (reversibleMonitoredModel 53 ε ρ hε hρ).total s=
      (reversibleFiniteModel 53 ε hε).total s+reversibleReverseHazard 53 ρ s := by
    simp [reversibleMonitoredModel,withExtraExit,FiniteJumpModel.total,Fintype.sum_option,add_comm]
  rw [he]
  norm_num at hb
  linarith

theorem reversible_joint_bounds (N : Nat) (data : Nat → Array Int)
    (hrows : ∀ m, N ≤ m → m < 2*N → ReversibleRows.checkLayer m (data m) (data (m+1))=true)
    (ht : ReversibleRows.terminalCheck N (data (2*N))=true) (word : Fin 2 → Fin 2)
    (s : CoupledFiniteState N) :
    coupledJointValue N data word s ≤ 1 ∧ 0 ≤ coupledJointTime N data s := by
  cases s with
  | none => norm_num [coupledJointValue,coupledJointTime]
  | some s =>
    rcases s with ⟨j,a⟩
    have h0 := reversible_current_bounds N data hrows ht ⟨j,a⟩ 0
    have h1 := reversible_current_bounds N data hrows ht ⟨j,a⟩ 1
    constructor
    · change coupledCurrent N data ⟨j,a⟩ 0 (word 0).val+
        coupledCurrent N data ⟨j,a⟩ 1 (word 1).val-1 ≤ 1
      linarith only [h0.1 (word 0),h1.1 (word 1)]
    · by_cases hj : j.val=N
      · simp [coupledJointTime,hj]
      · have he : coupledJointTime N data (some ⟨j,a⟩)=
            (coupledCurrent N data ⟨j,a⟩ 0 2+coupledCurrent N data ⟨j,a⟩ 1 2)/2 := by
          simp [coupledJointTime,coupledCurrent,hj]
          ring
        rw [he]
        linarith only [h0.2,h1.2]


/-- Explicit monitored finite model with positive reverse-growth hazard and a
finite chemical-event quota. Integer tables remain the only numerical premises. -/
theorem reversible_budgeted_uniform_deadline (ε ρ : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10)
    (hρ : 0 ≤ ρ) (hρu : ρ ≤ 2/10000000) (data : Nat → Array Int)
    (hrows : ∀ m, 53 ≤ m → m < 106 → ReversibleRows.checkLayer m (data m) (data (m+1))=true)
    (ht : ReversibleRows.terminalCheck 53 (data 106)=true)
    (hb : ReversibleRows.birthOK 53 (data 53)=true)
    (word : Fin 2 → Fin 2) (a : Fin 2 → Fin 849 × Fin 213)
    (ha : ∀ k, newborn 53 (word k).val (a k).1.val (a k).2.val) :
    (9901/10000 : ℝ) ≤ finiteTimeExpectation
      (eventBudgetModel (reversibleMonitoredModel 53 ε ρ hε hρ) 100000000) 20
      (budgetObservable 100000000 (coupledExactPayoff 53 word)) (some ⟨0,a⟩,0) := by
  have hg := reversible_checked_generators 53 (by norm_num) ε hε hε1 data hrows ht word
  have hw : coupledJointTime 53 data (some ⟨0,a⟩)=
      (coupledCurrent 53 data ⟨0,a⟩ 0 2+coupledCurrent 53 data ⟨0,a⟩ 1 2)/2 := by
    norm_num [coupledJointTime,coupledCurrent]
    ring
  have hb0 := reversible_initial_half_tail data hb word a ha 0
  have hb1 := reversible_initial_half_tail data hb word a ha 1
  have hbirth : (495550 : ℝ) ≤ 500000*coupledJointValue 53 data word (some ⟨0,a⟩)-
      2*coupledJointTime 53 data (some ⟨0,a⟩) := by
    rw [hw]
    change (495550 : ℝ) ≤ 500000*(coupledCurrent 53 data ⟨0,a⟩ 0 (word 0).val+
      coupledCurrent 53 data ⟨0,a⟩ 1 (word 1).val-1)-_
    linarith only [hb0,hb1]
  exact reversible_monitored_deadline (reversibleFiniteModel 53 ε hε) none
    (reversibleReverseHazard 53 ρ) (reversibleReverseHazard_nonneg 53 ρ hρ)
    (coupledExactPayoff 53 word) (coupledJointValue 53 data word) (coupledJointTime 53 data)
    rfl rfl (fun s => (reversible_joint_bounds 53 data hrows ht word s).1)
    (fun s => (reversible_joint_bounds 53 data hrows ht word s).2)
    (reversibleReverseHazard_bound ρ hρ hρu) (reversibleMonitored_total ε ρ hε hε1 hρ hρu)
    hg.1 hg.2 (reversible_value_cover 53 data hrows ht word) (some ⟨0,a⟩) hbirth

end CompositionalMemory
