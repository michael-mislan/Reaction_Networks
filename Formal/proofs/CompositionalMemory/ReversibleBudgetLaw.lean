import proofs.CompositionalMemory.ReversiblePhysicalBudget

namespace CompositionalMemory
open Classical FiniteCopy MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000
attribute [local irreducible] physicalSafeDeadline

instance (N : Nat) : MeasurableSpace (ReversiblePhysicalState N) := ⊤
instance (N : Nat) : MeasurableSingletonClass (ReversiblePhysicalState N) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

abbrev ReversibleBudgetState (N : Nat) := ReversiblePhysicalState N × Nat

def reversibleBudgetNext (N J : Nat) := countBudgetNext (reversiblePhysicalNext N) J

def reversibleBudgetRate (N : Nat) (ε ρ : ℝ) (z : ReversibleBudgetState N)
    (r : Option ReversiblePhysicalChannel) := reversiblePhysicalRate N ε ρ z.1 r

theorem reversibleBudgetRate_nonneg (N : Nat) (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (z : ReversibleBudgetState N) (r : Option ReversiblePhysicalChannel) :
    0 ≤ reversibleBudgetRate N ε ρ z r := reversiblePhysicalRate_nonneg N ε ρ hε hρ z.1 r

theorem reversibleBudgetRate_total_pos (N : Nat) (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (z : ReversibleBudgetState N) : 0 < ∑ r,reversibleBudgetRate N ε ρ z r :=
  reversiblePhysicalRate_total_pos N ε ρ hε hρ z.1

def reversibleBudgetEmbed (N J : Nat) := countBudgetEmbed (reversiblePhysicalEmbed N) J
def reversibleBudgetClip (N J : Nat) := countBudgetClip (reversiblePhysicalClip N) J

def reversibleBudgetPayoff (N J : Nat) (word : Fin 2 → Fin 2) (z : ReversibleBudgetState N) : ℝ≥0∞ :=
  ENNReal.ofReal (killedBudgetObservable J (coupledExactPayoff N word) (reversibleBudgetClip N J z))

theorem reversible_budget_observable_bounds (N J : Nat) (word : Fin 2 → Fin 2)
    (z : Option (CoupledLiveState N × Fin J)) :
    0 ≤ killedBudgetObservable J (coupledExactPayoff N word) z ∧
      killedBudgetObservable J (coupledExactPayoff N word) z ≤ 1 := by
  cases z with
  | none => norm_num [killedBudgetObservable]
  | some z => exact coupledExactPayoff_bounds N word (some z.1)

theorem reversible_budget_physical_law (N J : Nat) (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (word : Fin 2 → Fin 2) (s : CoupledLiveState N × Fin J) :
    physicalSafeDeadline (reversibleBudgetNext N J) (reversibleBudgetRate N ε ρ)
      (reversibleBudgetRate_nonneg N ε ρ hε hρ) (reversibleBudgetRate_total_pos N ε ρ hε hρ)
      {z | reversibleBudgetClip N J z≠none} (reversibleBudgetPayoff N J word)
      (reversibleBudgetEmbed N J s) 20 =
    ENNReal.ofReal (finiteTimeExpectation
      (killedBudgetModel (reversiblePhysicalEncodedModel N ε ρ hε hρ) J) 20
      (killedBudgetObservable J (coupledExactPayoff N word)) (some s)) := by
  let M := encodedFiniteModel (reversibleBudgetNext N J) (reversibleBudgetRate N ε ρ)
    (reversibleBudgetRate_nonneg N ε ρ hε hρ) (reversibleBudgetEmbed N J) (reversibleBudgetClip N J)
  have hleft := countBudget_clip_embed (reversiblePhysicalEmbed N) (reversiblePhysicalClip N)
    (reversiblePhysical_clip_embed N) J
  have hright := countBudget_embed_clip (reversiblePhysicalEmbed N) (reversiblePhysicalClip N)
    (reversiblePhysical_embed_clip N) J
  have hf (z : ReversibleBudgetState N) : reversibleBudgetPayoff N J word z ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (reversible_budget_observable_bounds N J word _).2
  have hpay : encodedValue (reversibleBudgetEmbed N J) (reversibleBudgetPayoff N J word)=
      fun z => ENNReal.ofReal (killedBudgetObservable J (coupledExactPayoff N word) z) := by
    funext z
    cases z with
    | none => simp [encodedValue,killedBudgetObservable]
    | some z =>
      change ENNReal.ofReal (killedBudgetObservable J (coupledExactPayoff N word)
        (countBudgetClip (reversiblePhysicalClip N) J (countBudgetEmbed (reversiblePhysicalEmbed N) J z)))=_
      rw [hleft]
  obtain ⟨q,hq,_,hb⟩ := M.exists_clock 0
  have he := encoded_source_identification (reversibleBudgetNext N J) (reversibleBudgetRate N ε ρ)
    (reversibleBudgetRate_nonneg N ε ρ hε hρ) (reversibleBudgetRate_total_pos N ε ρ hε hρ)
    (reversibleBudgetEmbed N J) (reversibleBudgetClip N J) hleft hright
    (reversibleBudgetPayoff N J word) hf q hq hb s 20
  rw [he,hpay]
  rw [causalSafeClock,if_pos (by norm_num : (0 : ℝ) ≤ 20)]
  have hs := safeClockPayoff_univ (M.uniformize q hq hb)
    (killedBudgetObservable J (coupledExactPayoff N word))
    (fun z => (reversible_budget_observable_bounds N J word z).1)
    (fun z => (reversible_budget_observable_bounds N J word z).2) q 20 (some s)
  norm_num at hs
  change _=ENNReal.ofReal _ at hs
  rw [hs]
  have hu := finite_time_eq_uniformized M q 20 hq hb
    (killedBudgetObservable J (coupledExactPayoff N word)) (some s)
  rw [← hu]
  have hM : M=killedBudgetModel (reversiblePhysicalEncodedModel N ε ρ hε hρ) J :=
    countBudget_model_encoding (reversiblePhysicalNext N) (reversiblePhysicalRate N ε ρ)
      (reversiblePhysicalRate_nonneg N ε ρ hε hρ) (reversiblePhysicalEmbed N) (reversiblePhysicalClip N) J
  rw [hM]

end
end CompositionalMemory
