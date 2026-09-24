import proofs.RandomViability.CutoffAgreement
import proofs.RandomViability.JumpClockKernel

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy ProbabilityTheory
noncomputable section
set_option maxHeartbeats 30000

def unboundedPhysicalNext {n : ℕ} (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) : Molecule n → ℕ :=
  if ∀ z, physicalChannelInput ch z ≤ N z then
    applyCountChannel N (physicalChannelInput ch) (physicalChannelOutput ch) else N

def unboundedPhysicalRate {n : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) : ℝ :=
  if ∀ z, physicalChannelInput ch z ≤ N z then physicalChannelRate c V D basal cat N ch else 0

theorem unboundedPhysicalRate_nonneg {n : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) : 0 ≤ unboundedPhysicalRate c V D basal cat N ch := by
  unfold unboundedPhysicalRate
  split_ifs
  · unfold physicalChannelRate
    positivity
  · exact le_rfl

theorem unbounded_feed_rate {n : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (f : ↥(binaryFood n 2)) :
    unboundedPhysicalRate c V D basal cat N (.inl (.inl f)) = (D : ℝ)*V := by
  simp [unboundedPhysicalRate, physicalChannelInput, physicalChannelRate, physicalChannelCoefficient]

theorem unbounded_total_pos {n : ℕ} (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ) :
    0 < ∑ ch, unboundedPhysicalRate c V D basal cat N ch := by
  have hc : Fintype.card ↥(binaryFood n 2) = 6 :=
    (Fintype.card_congr (foodWordEquiv hn)).trans (by decide)
  have hne : Nonempty ↥(binaryFood n 2) := Fintype.card_pos_iff.mp (by rw [hc]; norm_num)
  obtain ⟨f⟩ := hne
  have hh := Finset.single_le_sum (f := unboundedPhysicalRate c V D basal cat N)
    (fun ch _ => unboundedPhysicalRate_nonneg c V D basal cat N ch)
    (Finset.mem_univ (.inl (.inl f)))
  rw [unbounded_feed_rate] at hh
  exact lt_of_lt_of_le (mul_pos hD hV) hh

theorem bounded_unbounded_rate_agree {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (ch : PhysicalCountChannel n) :
    (boundedPhysicalCountModel c V D basal cat).rate N ch =
      unboundedPhysicalRate c V D basal cat (boundedCountsValue N) ch := rfl

theorem bounded_unbounded_next_agree {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (ch : PhysicalCountChannel n) (hB : boundedMass N+foodInputMass ch ≤ B) :
    boundedCountsValue ((boundedPhysicalCountModel c V D basal cat).next N ch) =
      unboundedPhysicalNext (boundedCountsValue N) ch := by
  by_cases he : ∀ z, physicalChannelInput ch z ≤ boundedCountsValue N z
  · change boundedCountsValue (if _ then _ else N) = if _ then _ else _
    rw [if_pos he, if_pos he]
    exact truncateCounts_preserves N _ ((physical_raw_mass_le_input _ ch he).trans hB)
  · change boundedCountsValue (if _ then _ else N) = if _ then _ else _
    rw [if_neg he, if_neg he]

def physicalJumpClockKernel {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
    (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) :
    Kernel (Molecule n → ℕ) (PhysicalCountChannel n × ℝ) :=
  jumpClockKernel (unboundedPhysicalRate c V D basal cat)
    (unboundedPhysicalRate_nonneg c V D basal cat) (unbounded_total_pos hn c V D hV hD basal cat)

instance physicalJumpClockKernel_markov {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
    (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) :
    IsMarkovKernel (physicalJumpClockKernel hn c V D hV hD basal cat) := by
  unfold physicalJumpClockKernel
  infer_instance

end
end RandomViability
