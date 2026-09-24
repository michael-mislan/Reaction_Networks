import proofs.SerialTransferSelection.NewbornPhase
import proofs.SerialTransferSelection.CycleMaterial

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

/-- A physical expenditure cutoff; a rejected event halts the apparatus. -/
def budgetRun {α β : Type*} [Fintype α] [Fintype β]
    (model : FiniteJumpModel α β) (cost : β → ℕ) : ℕ → α → List β → α
  | _, s, [] => s
  | B, s, r::rs => if cost r ≤ B then budgetRun model cost (B-cost r) (model.next s r) rs else s

/-- The same event word has the same outcome whenever its expenditure fits. -/
theorem hard_budget_agreement {α β : Type*} [Fintype α] [Fintype β]
    (model : FiniteJumpModel α β) (cost : β → ℕ) (B : ℕ) (s : α) (rs : List β)
    (h : (rs.map cost).sum ≤ B) : budgetRun model cost B s rs=eventRun model s rs := by
  induction rs generalizing B s with
  | nil => rfl
  | cons r rs ih =>
    have hh : cost r+(rs.map cost).sum ≤ B := h
    have hr : cost r ≤ B := by omega
    simp only [budgetRun,if_pos hr,eventRun]
    exact ih (B-cost r) (model.next s r) (by omega)

theorem unsaturated_budget_agreement {α β : Type*} [Fintype α] [Fintype β]
    (model : FiniteJumpModel α β) (J : ℕ) (s : α) (rs : List β)
    (cost : β → ℕ) (hc : ∀ r, cost r ≤ 1)
    (hs : (eventRun (serviceCounterModel model J) (s,0) rs).2.val < J) :
    budgetRun model cost J s rs=eventRun model s rs := by
  exact hard_budget_agreement model cost J s rs (service_run_material_budget model J s rs cost hc hs).le

noncomputable def explicitQuota (exposure : ℝ) : ℕ := Nat.ceil (1000*exposure)+1

theorem explicit_quota_bound (exposure : ℝ) (_h : 0 ≤ exposure) :
    0 < explicitQuota exposure ∧ exposure/(explicitQuota exposure : ℝ) < 1/1000 := by
  have he : 1000*exposure ≤ (Nat.ceil (1000*exposure) : ℝ) := Nat.le_ceil _
  have hj : 0 < explicitQuota exposure := by unfold explicitQuota; omega
  refine ⟨hj,?_⟩
  apply (div_lt_iff₀ (by exact_mod_cast hj : (0 : ℝ) < explicitQuota exposure)).mpr
  simp only [explicitQuota,Nat.cast_add,Nat.cast_one]
  linarith only [he]

theorem newborn_membrane (N : ℕ) (cs : List TaggedCell)
    (h : ∀ c ∈ cs, c.compartment.2=N) : membrane cs=N*cs.length := by
  induction cs with
  | nil => simp [membrane]
  | cons c cs ih =>
    have hc := h c (by simp)
    have ht := ih (fun d hd => h d (by simp [hd]))
    simp only [membrane_cons,List.length_cons,hc,ht]
    ring

theorem newborn_two_cycle_growth_stock (N M : ℕ) (s t : PopulationState)
    (hs : s.live.length=M) (ht : t.live.length=M)
    (hn : ∀ c ∈ s.live, c.compartment.2=N) (hvt : ValidVolumes N t) :
    4*membrane s.live+4*membrane t.live ≤ 12*N*M := by
  have h0 := newborn_membrane N s.live hn
  have h1 := membrane_upper N t.live (fun c hc => (hvt c hc).2.le)
  rw [hs] at h0
  rw [ht] at h1
  nlinarith only [h0,h1]

theorem measured_fraction_difference (f0 f1 measured0 measured1 rho : ℝ)
    (h0 : |measured0-f0| ≤ rho) (h1 : |measured1-f1| ≤ rho) :
    f1-f0-2*rho ≤ measured1-measured0 := by
  have a := abs_le.mp h0
  have b := abs_le.mp h1
  linarith only [a.2,b.1]

theorem observable_increase (f0 f1 measured0 measured1 rho delta : ℝ)
    (h0 : |measured0-f0| ≤ rho) (h1 : |measured1-f1| ≤ rho)
    (hg : delta < f1-f0) (hr : rho < delta/2) : measured0 < measured1 := by
  have h := measured_fraction_difference f0 f1 measured0 measured1 rho h0 h1
  linarith only [h,hg,hr]

end SerialTransferSelection
