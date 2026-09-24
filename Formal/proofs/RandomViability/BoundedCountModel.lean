import proofs.RandomViability.CountTruncation
import proofs.PowerLawSmallRAF.SourcePowerLawTraceProbability
import proofs.FiniteCopy.FiniteJump

namespace RandomViability
open Classical RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section

/-- Food inflow, molecular outflow, reversible basal pairs, and reversible
selected catalytic pairs. True is ligation; false is cleavage. -/
abbrev PhysicalCountChannel (n : ℕ) :=
  (↥(binaryFood n 2) ⊕ Molecule n) ⊕
    ((Reaction n × Bool) ⊕ (Reaction n × Molecule n × Bool))

def physicalChannelInput {n : ℕ} : PhysicalCountChannel n → Molecule n → ℕ
  | .inl (.inl _) => fun _ => 0
  | .inl (.inr z) => singleCount z
  | .inr (.inl (r,d)) => if d then
      (fun z => singleCount (reactionLeft r) z + singleCount (reactionRight r) z)
    else singleCount (reactionProduct r)
  | .inr (.inr (r,c,d)) => if d then
      (fun z => singleCount (reactionLeft r) z + singleCount (reactionRight r) z + singleCount c z)
    else (fun z => singleCount (reactionProduct r) z + singleCount c z)

def physicalChannelOutput {n : ℕ} : PhysicalCountChannel n → Molecule n → ℕ
  | .inl (.inl z) => singleCount z.val
  | .inl (.inr _) => fun _ => 0
  | .inr (.inl (r,d)) => if d then singleCount (reactionProduct r) else
      (fun z => singleCount (reactionLeft r) z + singleCount (reactionRight r) z)
  | .inr (.inr (r,c,d)) => if d then
      (fun z => singleCount (reactionProduct r) z + singleCount c z)
    else (fun z => singleCount (reactionLeft r) z + singleCount (reactionRight r) z + singleCount c z)

/-- Shared coefficients in the two directions implement the adopted
length-additive equilibrium-ratio-one family. -/
def physicalChannelCoefficient {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (D : NNReal) (basal : Reaction n → NNReal)
    (catalytic : Reaction n → Molecule n → NNReal) : PhysicalCountChannel n → NNReal
  | .inl _ => D
  | .inr (.inl (r,_)) => basal r
  | .inr (.inr (r,z,_)) => if r ∈ c z then catalytic r z else 0

def physicalChannelRate {n : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) : ℝ :=
  (physicalChannelCoefficient c D basal catalytic ch : ℝ) * (V : ℝ) *
    (∏ z, ((N z).descFactorial (physicalChannelInput ch z) : ℝ)) /
    (V : ℝ)^(∑ z, physicalChannelInput ch z)

/-- The actual finite reaction model with a total-mass cutoff. Only attempted
updates outside the finite state set become self-loops. -/
def boundedPhysicalCountModel {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal) :
    FiniteJumpModel (BoundedCounts n B) (PhysicalCountChannel n) where
  next N ch := if ∀ z, physicalChannelInput ch z ≤ boundedCountsValue N z then
      truncateCounts N (applyCountChannel (boundedCountsValue N) (physicalChannelInput ch) (physicalChannelOutput ch))
    else N
  rate N ch := if ∀ z, physicalChannelInput ch z ≤ boundedCountsValue N z then
      physicalChannelRate c V D basal catalytic (boundedCountsValue N) ch
    else 0
  nonneg N ch := by
    split_ifs
    · unfold physicalChannelRate
      positivity
    · exact le_rfl

theorem physical_basal_channel_balanced {n : ℕ} (r : Reaction n) (d : Bool) :
    countMass (physicalChannelInput (.inr (.inl (r,d)))) =
      countMass (physicalChannelOutput (.inr (.inl (r,d)))) := by
  cases d
  · exact (basal_count_channel_balance r).symm
  · exact basal_count_channel_balance r

theorem physical_catalytic_channel_balanced {n : ℕ} (r : Reaction n) (z : Molecule n) (d : Bool) :
    countMass (physicalChannelInput (.inr (.inr (r,z,d)))) =
      countMass (physicalChannelOutput (.inr (.inr (r,z,d)))) := by
  cases d
  · exact (catalytic_count_channel_balance r z).symm
  · exact catalytic_count_channel_balance r z

end
end RandomViability
