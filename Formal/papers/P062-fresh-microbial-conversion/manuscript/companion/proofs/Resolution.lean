import proofs.MicrobialFunctionAssay.Certificate

namespace MicrobialFunctionAssay
noncomputable section

def firstWitness : Window where
  p0 := 8; r0 := 2; fresh := 0; release := 0; uptake := 0
  collect := 6; lossP := 0; lossR := 0
  nonneg := by norm_num
  enoughR := by norm_num
  enoughP := by norm_num
  release_available := by norm_num

def secondWitness : Window where
  p0 := 1/10; r0 := 9/5; fresh := 21/10; release := 39/10; uptake := 0
  collect := 4; lossP := 0; lossR := 0
  nonneg := by norm_num
  enoughR := by norm_num
  enoughP := by norm_num
  release_available := by norm_num

def witness : History where
  first := firstWitness; second := secondWitness
  e := 1/20; s := 9/10; inputP := 0; inputR := 0
  fractions := by norm_num
  inputs_nonneg := by norm_num
  p_recovery := by norm_num [firstWitness, secondWitness, Window.p]
  r_recovery := by norm_num [firstWitness, secondWitness, Window.r]

theorem witness_useful :
    lower (29/5) (19/5) 10 witness.e witness.s 2 (1/5) = 169/100 ∧
    witness.first.fresh+witness.second.fresh = 21/10 := by
  norm_num [lower, witness, firstWitness, secondWitness]

/-- Exact main source-bound robust decision, with a separately proved inhabitant. -/
theorem resolution (h : History)
    (he : h.e=1/20) (hs : h.s=9/10)
    (ho1 : |h.first.collect-6| ≤ 1/5)
    (ho2 : |h.second.collect-4| ≤ 1/5)
    (hB : h.first.p0+h.first.r0 ≤ 10) (hJ : h.first.r ≤ 2)
    (hH : h.inputP+h.inputR ≤ 1/5) :
    169/100 ≤ h.first.fresh+h.second.fresh := by
  apply reporting h 6 4 (1/5) (1/5) 10 2 (1/5) (169/100) ho1 ho2 hB hJ hH
  rw [he, hs]
  norm_num [lower]

theorem witness_satisfies_root :
    |witness.first.collect-6| ≤ (1/5:ℝ) ∧
    |witness.second.collect-4| ≤ (1/5:ℝ) ∧
    witness.first.p0+witness.first.r0 ≤ 10 ∧ witness.first.r ≤ 2 ∧
    witness.inputP+witness.inputR ≤ (1/5:ℝ) := by
  norm_num [witness, firstWitness, secondWitness, Window.r]

end
end MicrobialFunctionAssay
