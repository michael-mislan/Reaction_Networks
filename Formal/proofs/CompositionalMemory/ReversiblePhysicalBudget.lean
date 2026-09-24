import proofs.CompositionalMemory.ReversiblePhysicalEncoding
import proofs.CompositionalMemory.CountBudgetEncoding
import proofs.CompositionalMemory.FiniteQuotaTransport

namespace CompositionalMemory
open FiniteCopy ControlledRows

theorem reversiblePhysical_total_live (N : Nat) (hN : 0 < N) (ε ρ : ℝ)
    (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (s : CoupledLiveState N) :
    (reversiblePhysicalEncodedModel N ε ρ hε hρ).total (some s)=
      (reversibleFiniteModel N ε hε).total (some s)+reversibleReverseHazard N ρ (some s)+1 := by
  have hsum (k : Fin 2) :
      (∑ r : Fin 14,reversiblePhysicalReactionRate N ε ρ (reversiblePhysicalEmbed N s) (k,r))=
      (∑ r : Fin 13,reversibleRate N ε (some s) (k,r))+
        (if s.1.val=N then 0 else ρ*((N : ℝ)+s.1.val)) := by
    rw [Fin.sum_univ_castSucc]
    simp_rw [reversiblePhysical_first_rate N hN,reversiblePhysical_reverse_rate N hN]
  simp only [FiniteJumpModel.total,reversiblePhysicalEncodedModel,encodedFiniteModel,
    Fintype.sum_option,reversiblePhysicalRate,Fintype.sum_prod_type]
  simp_rw [hsum]
  simp only [reversibleFiniteModel,Finset.sum_add_distrib]
  rcases s with ⟨j,a⟩
  by_cases hj : j.val=N
  · simp [reversibleReverseHazard,hj,Fin.sum_univ_two]
    ring
  · simp [reversibleReverseHazard,hj,Fin.sum_univ_two]
    ring

theorem reversiblePhysical_total_bound (ε ρ : ℝ) (hε : 0 ≤ ε) (hεu : ε ≤ 1/10)
    (hρ : 0 ≤ ρ) (hρu : ρ ≤ 2/10000000) (s : CoupledFiniteState 53) :
    (reversiblePhysicalEncodedModel 53 ε ρ hε hρ).total s ≤ 4000000 := by
  cases s with
  | none => simp [FiniteJumpModel.total,reversiblePhysicalEncodedModel,encodedFiniteModel]
  | some s =>
    rw [reversiblePhysical_total_live 53 (by norm_num)]
    have hb := reversible_total_rate_cap 53 (by norm_num) ε hε hεu (some s)
    have hk := reversibleReverseHazard_bound ρ hρ hρu (some s)
    norm_num at hb
    linarith

/-- The event budget includes the auxiliary clock, so the chemical inventory
bound is conservative. Its counter is encoded from the actual count source. -/
theorem reversible_physical_budget_deadline (ε ρ : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10)
    (hρ : 0 ≤ ρ) (hρu : ρ ≤ 2/10000000) (data : Nat → Array Int)
    (hrows : ∀ m, 53 ≤ m → m < 106 → ReversibleRows.checkLayer m (data m) (data (m+1))=true)
    (ht : ReversibleRows.terminalCheck 53 (data 106)=true)
    (hb : ReversibleRows.birthOK 53 (data 53)=true)
    (word : Fin 2 → Fin 2) (a : Fin 2 → Fin 849 × Fin 213)
    (ha : ∀ k, newborn 53 (word k).val (a k).1.val (a k).2.val) :
    (9901/10000 : ℝ) ≤ finiteTimeExpectation
      (killedBudgetModel (reversiblePhysicalEncodedModel 53 ε ρ hε hρ) 100000000) 20
      (killedBudgetObservable 100000000 (coupledExactPayoff 53 word))
      (some (⟨0,a⟩,(0 : Fin 100000000))) := by
  have hg := reversible_checked_generators 53 (by norm_num) ε hε hε1 data hrows ht word
  have hbounds := reversible_joint_bounds 53 data hrows ht word
  have hm := extra_exit_generators (reversibleFiniteModel 53 ε hε) none
    (reversibleReverseHazard 53 ρ) (reversibleReverseHazard_nonneg 53 ρ hρ)
    (coupledJointValue 53 data word) (coupledJointTime 53 data)
    (2/1000000) (1/50000) (5/8) (53/1250000) rfl rfl
    (fun s => (hbounds s).1) (fun s => (hbounds s).2)
    (reversibleReverseHazard_bound ρ hρ hρu) hg.1 hg.2
  have hv : ∀ s, -(2/1000000+53/1250000 : ℝ) ≤
      (reversiblePhysicalEncodedModel 53 ε ρ hε hρ).generator (coupledJointValue 53 data word) s := by
    intro s
    rw [reversiblePhysical_encoded_generator 53 (by norm_num)]
    exact hm.1 s
  have hw : ∀ s, (reversiblePhysicalEncodedModel 53 ε ρ hε hρ).generator (coupledJointTime 53 data) s ≤
      -(5/8 : ℝ)*coupledJointTime 53 data s+1/50000 := by
    intro s
    rw [reversiblePhysical_encoded_generator 53 (by norm_num)]
    exact hm.2 s
  have hh := killed_quota_deadline (reversiblePhysicalEncodedModel 53 ε ρ hε hρ)
    (coupledExactPayoff 53 word)
    (coupledJointValue 53 data word) (coupledJointTime 53 data)
    (2/1000000+53/1250000) (1/50000) (5/8)
    (by norm_num) (by norm_num) (by norm_num)
    (fun _ => rfl) rfl
    (fun s => (hbounds s).1) (fun s => (hbounds s).2)
    (reversiblePhysical_total_bound ε ρ hε hε1 hρ hρu) hv hw
    (reversible_value_cover 53 data hrows ht word) ⟨0,a⟩
  have he : coupledJointTime 53 data (some ⟨0,a⟩)=
      (coupledCurrent 53 data ⟨0,a⟩ 0 2+coupledCurrent 53 data ⟨0,a⟩ 1 2)/2 := by
    norm_num [coupledJointTime,coupledCurrent]
    ring
  have hb0 := reversible_initial_half_tail data hb word a ha 0
  have hb1 := reversible_initial_half_tail data hb word a ha 1
  have hbirth : (495550 : ℝ) ≤ 500000*coupledJointValue 53 data word (some ⟨0,a⟩)-
      2*coupledJointTime 53 data (some ⟨0,a⟩) := by
    rw [he]
    change (495550 : ℝ) ≤ 500000*(coupledCurrent 53 data ⟨0,a⟩ 0 (word 0).val+
      coupledCurrent 53 data ⟨0,a⟩ 1 (word 1).val-1)-_
    linarith only [hb0,hb1]
  norm_num at hh
  have htail := mul_le_mul_of_nonneg_right wide_deadline_exp_bound (hbounds (some ⟨0,a⟩)).2
  nlinarith only [hh,htail,hbirth]

end CompositionalMemory
