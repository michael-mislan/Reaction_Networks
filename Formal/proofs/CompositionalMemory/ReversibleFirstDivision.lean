import proofs.CompositionalMemory.ReversibleBudgetLaw
import proofs.RandomViability.JumpSupport

namespace CompositionalMemory
open Classical RandomViability MeasureTheory ProbabilityTheory ControlledRows
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

abbrev ReversibleBudgetPath (N : Nat) :=
  Nat → JumpState (ReversibleBudgetState N) (Option ReversiblePhysicalChannel)

def reversibleBudgetCounts (N : Nat) (s : ReversibleBudgetState N) := reversiblePhysicalCounts N s.1

def reversibleParentReward (N : Nat) (word : Fin 2 → Fin 2) (s : ReversibleBudgetState N) : ℝ≥0∞ :=
  let a := (reversibleBudgetCounts N s).2
  ENNReal.ofReal (terminalReward N (a 0).1.toNat (a 0).2.toNat (word 0).val*
    terminalReward N (a 1).1.toNat (a 1).2.toNat (word 1).val)

def reversibleFirstDivisionAt (N : Nat) (z : ReversibleBudgetPath N) (k : Nat) : Prop :=
  (reversibleBudgetCounts N (z k).1).1=2*N ∧
    ∀ i < k, (reversibleBudgetCounts N (z i).1).1≠2*N

def reversibleFirstDivisionPayoff (N : Nat) (word : Fin 2 → Fin 2) (T : ℝ)
    (z : ReversibleBudgetPath N) : ℝ≥0∞ :=
  ∑' k, if reversibleFirstDivisionAt N z k ∧ jumpElapsed z k ≤ T then
    reversibleParentReward N word (z k).1 else 0

theorem reversibleCountReactionNext_terminal (N : Nat) (s : CoupledCountState N)
    (hs : s.1.val=N) (r : ReversibleChannel) : reversibleCountReactionNext N s r=s := by
  by_cases hr : r.2.val<8
  · simp [reversibleCountReactionNext,hr,coupledCountReactionNext,hs]
  · simp [reversibleCountReactionNext,hr,hs]

theorem reversiblePhysicalNext_terminal (N : Nat) (s : ReversiblePhysicalState N)
    (hs : (reversiblePhysicalCounts N s).1=2*N) (r : Option ReversiblePhysicalChannel) :
    reversiblePhysicalNext N s r=s := by
  cases r with
  | none => rfl
  | some r =>
    cases s with
    | inl s =>
      have hj : s.1.val=N := by change N+s.1.val=2*N at hs; omega
      by_cases hr : r.2.val<13
      · simp [reversiblePhysicalNext,reversiblePhysicalReactionNext,hr,
          reversibleCountReactionNext_terminal N s hj]
      · simp [reversiblePhysicalNext,reversiblePhysicalReactionNext,hr,hj]
    | inr s =>
      change s.1=2*N at hs
      simp [reversiblePhysicalNext,reversiblePhysicalReactionNext,reversibleRawNext,hs]

theorem reversibleBudgetNext_terminal_counts (N J : Nat) (s : ReversibleBudgetState N)
    (hs : (reversibleBudgetCounts N s).1=2*N) (r : Option ReversiblePhysicalChannel) :
    reversibleBudgetCounts N (reversibleBudgetNext N J s r)=reversibleBudgetCounts N s := by
  simp only [reversibleBudgetNext,countBudgetNext]
  split_ifs
  · exact congrArg (reversiblePhysicalCounts N) (reversiblePhysicalNext_terminal N s.1 hs r)
  · rfl

theorem reversible_terminal_persists (N J : Nat) (z : ReversibleBudgetPath N)
    (hz : ∀ k, jumpConsistent (reversibleBudgetNext N J) (z k).1 (z (k+1)))
    (j k : Nat) (hj : (reversibleBudgetCounts N (z j).1).1=2*N) (hjk : j ≤ k) :
    reversibleBudgetCounts N (z k).1=reversibleBudgetCounts N (z j).1 := by
  induction k,hjk using Nat.le_induction with
  | base => rfl
  | succ k _ ih =>
    obtain ⟨b,_,hb⟩ := hz k
    rw [hb,reversibleBudgetNext_terminal_counts N J _ (by rw [ih]; exact hj)]
    exact ih

theorem reversibleBudgetPayoff_le_parent (N J : Nat) (word : Fin 2 → Fin 2) (z : ReversibleBudgetState N) :
    reversibleBudgetPayoff N J word z ≤
      if (reversibleBudgetCounts N z).1=2*N then reversibleParentReward N word z else 0 := by
  cases hc : reversibleBudgetClip N J z with
  | none => simp [reversibleBudgetPayoff,hc,killedBudgetObservable]
  | some s =>
    have he := countBudget_embed_clip (reversiblePhysicalEmbed N) (reversiblePhysicalClip N)
      (reversiblePhysical_embed_clip N) J z s hc
    change reversibleBudgetEmbed N J s=z at he
    rw [← he]
    have hleft := countBudget_clip_embed (reversiblePhysicalEmbed N) (reversiblePhysicalClip N)
      (reversiblePhysical_clip_embed N) J s
    change reversibleBudgetClip N J (reversibleBudgetEmbed N J s)=some s at hleft
    simp only [reversibleBudgetPayoff,hleft]
    rcases s with ⟨⟨j,a⟩,c⟩
    by_cases h : j.val=N <;>
      simp [killedBudgetObservable,coupledExactPayoff,reversibleParentReward,reversibleBudgetCounts,
        reversibleBudgetEmbed,countBudgetEmbed,reversiblePhysicalEmbed,reversiblePhysicalCounts,
        coupledCountEmbed,h,two_mul]

theorem reversible_safe_payoff_le_first (N J : Nat) (word : Fin 2 → Fin 2) (T : ℝ)
    (z : ReversibleBudgetPath N)
    (hz : ∀ k, jumpConsistent (reversibleBudgetNext N J) (z k).1 (z (k+1))) :
    safeDeadlinePayoff {s | reversibleBudgetClip N J s≠none} (reversibleBudgetPayoff N J word) T z ≤
      reversibleFirstDivisionPayoff N word T z := by
  by_cases he : ∃ k, safeDeadlineIndex {s | reversibleBudgetClip N J s≠none} T z k
  · obtain ⟨k,hk⟩ := he
    rw [safeDeadlinePayoff_eq _ _ _ z hk]
    have hp := reversibleBudgetPayoff_le_parent N J word (z k).1
    by_cases hd : (reversibleBudgetCounts N (z k).1).1=2*N
    · simp only [if_pos hd] at hp
      have hex : ∃ j, (reversibleBudgetCounts N (z j).1).1=2*N := ⟨k,hd⟩
      let j := Nat.find hex
      have hj : (reversibleBudgetCounts N (z j).1).1=2*N := Nat.find_spec hex
      have hjk : j ≤ k := Nat.find_min' hex hd
      have hfirst : reversibleFirstDivisionAt N z j := ⟨hj,fun i hi => Nat.find_min hex hi⟩
      have htime : jumpElapsed z j ≤ T := (hk.1 j hjk).2
      have hstate := reversible_terminal_persists N J z hz j k hj hjk
      have hparent : reversibleParentReward N word (z k).1=reversibleParentReward N word (z j).1 := by
        simp only [reversibleParentReward,hstate]
      apply hp.trans
      rw [hparent]
      change reversibleParentReward N word (z j).1 ≤ ∑' i,
        if reversibleFirstDivisionAt N z i ∧ jumpElapsed z i ≤ T then reversibleParentReward N word (z i).1 else 0
      calc
        _ = (if reversibleFirstDivisionAt N z j ∧ jumpElapsed z j ≤ T then
            reversibleParentReward N word (z j).1 else 0) := (if_pos ⟨hfirst,htime⟩).symm
        _ ≤ _ := ENNReal.le_tsum j
    · simp only [if_neg hd] at hp
      exact hp.trans zero_le
  · have hz0 : safeDeadlinePayoff {s | reversibleBudgetClip N J s≠none} (reversibleBudgetPayoff N J word) T z=0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro k
      exact if_neg (fun h => he ⟨k,h⟩)
    rw [hz0]
    exact zero_le

theorem reversibleFirstDivisionAt_measurable (N k : Nat) :
    MeasurableSet {z | reversibleFirstDivisionAt N z k} := by
  have hd (i : Nat) : MeasurableSet {z : ReversibleBudgetPath N |
      (reversibleBudgetCounts N (z i).1).1=2*N} :=
    (Set.to_countable {s : ReversibleBudgetState N | (reversibleBudgetCounts N s).1=2*N}).measurableSet.preimage
      (measurable_pi_apply i).fst
  have hi : MeasurableSet {z : ReversibleBudgetPath N |
      ∀ i < k, (reversibleBudgetCounts N (z i).1).1≠2*N} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ => (hd i).compl))
  exact (hd k).inter hi

theorem reversibleFirstDivisionPayoff_measurable (N : Nat) (word : Fin 2 → Fin 2) (T : ℝ) :
    Measurable (reversibleFirstDivisionPayoff N word T) := by
  apply Measurable.tsum
  intro k
  exact Measurable.ite ((reversibleFirstDivisionAt_measurable N k).inter
    (measurableSet_le (jumpElapsed_measurable k) measurable_const))
    ((measurable_of_countable (reversibleParentReward N word)).comp (measurable_pi_apply k).fst) measurable_const

theorem reversibleFirstDivisionAt_unique (N : Nat) (z : ReversibleBudgetPath N) (j k : Nat)
    (hj : reversibleFirstDivisionAt N z j) (hk : reversibleFirstDivisionAt N z k) : j=k := by
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact hk.2 j hlt hj.1
  · exact hj.2 k hgt hk.1

theorem reversibleParentReward_le_one (N : Nat) (word : Fin 2 → Fin 2) (s : ReversibleBudgetState N) :
    reversibleParentReward N word s ≤ 1 := by
  apply ENNReal.ofReal_le_one.mpr
  let a := (reversibleBudgetCounts N s).2
  have h0 := terminalReward_bounds N (a 0).1.toNat (a 0).2.toNat (word 0).val
  have h1 := terminalReward_bounds N (a 1).1.toNat (a 1).2.toNat (word 1).val
  exact (mul_le_mul h0.2 h1.2 h1.1 (by norm_num : (0 : ℝ) ≤ 1)).trans (by norm_num)

theorem reversibleFirstDivisionPayoff_le_one (N : Nat) (word : Fin 2 → Fin 2) (T : ℝ)
    (z : ReversibleBudgetPath N) : reversibleFirstDivisionPayoff N word T z ≤ 1 := by
  by_cases he : ∃ k, reversibleFirstDivisionAt N z k ∧ jumpElapsed z k ≤ T
  · obtain ⟨k,hk⟩ := he
    unfold reversibleFirstDivisionPayoff
    rw [tsum_eq_single k]
    · rw [if_pos hk]
      exact reversibleParentReward_le_one _ _ _
    · intro j hj
      exact if_neg (fun hh => hj (reversibleFirstDivisionAt_unique N z j k hh.1 hk.1))
  · have hh : reversibleFirstDivisionPayoff N word T z=0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro k
      exact if_neg (fun hk => he ⟨k,hk⟩)
    rw [hh]
    exact zero_le

def reversibleFirstDivisionReturn (N J : Nat) (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (word : Fin 2 → Fin 2) (initial : ReversibleBudgetState N) : ℝ≥0∞ :=
  ∫⁻ z,reversibleFirstDivisionPayoff N word 20 z ∂jumpTrajectoryLaw initial (reversibleBudgetNext N J)
    (reversibleBudgetRate N ε ρ) (reversibleBudgetRate_nonneg N ε ρ hε hρ)
    (reversibleBudgetRate_total_pos N ε ρ hε hρ)

theorem reversible_actual_first_division_from_checks (ε ρ : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10)
    (hρ : 0 ≤ ρ) (hρu : ρ ≤ 2/10000000) (data : Nat → Array Int)
    (hrows : ∀ m, 53 ≤ m → m < 106 → ReversibleRows.checkLayer m (data m) (data (m+1))=true)
    (ht : ReversibleRows.terminalCheck 53 (data 106)=true)
    (hb : ReversibleRows.birthOK 53 (data 53)=true)
    (word : Fin 2 → Fin 2) (a : Fin 2 → Fin 849 × Fin 213)
    (ha : ∀ k, newborn 53 (word k).val (a k).1.val (a k).2.val) :
    ENNReal.ofReal (9901/10000 : ℝ) ≤ reversibleFirstDivisionReturn 53 100000000 ε ρ hε hρ word
      (reversibleBudgetEmbed 53 100000000 (⟨0,a⟩,0)) := by
  have hf := reversible_physical_budget_deadline ε ρ hε hε1 hρ hρu data hrows ht hb word a ha
  have hsafe : ENNReal.ofReal (9901/10000 : ℝ) ≤
      physicalSafeDeadline (reversibleBudgetNext 53 100000000) (reversibleBudgetRate 53 ε ρ)
        (reversibleBudgetRate_nonneg 53 ε ρ hε hρ) (reversibleBudgetRate_total_pos 53 ε ρ hε hρ)
        {z | reversibleBudgetClip 53 100000000 z≠none} (reversibleBudgetPayoff 53 100000000 word)
        (reversibleBudgetEmbed 53 100000000 (⟨0,a⟩,0)) 20 := by
    rw [reversible_budget_physical_law 53 100000000 ε ρ hε hρ]
    exact ENNReal.ofReal_le_ofReal hf
  apply hsafe.trans
  apply lintegral_mono_ae
  filter_upwards [jumpTrajectory_consistent (reversibleBudgetEmbed 53 100000000 (⟨0,a⟩,0))
    (reversibleBudgetNext 53 100000000) (reversibleBudgetRate 53 ε ρ)
    (reversibleBudgetRate_nonneg 53 ε ρ hε hρ) (reversibleBudgetRate_total_pos 53 ε ρ hε hρ)] with z hz
  exact reversible_safe_payoff_le_first 53 100000000 word 20 z hz

end
end CompositionalMemory
