import proofs.RandomViability.QuietAllowedPaths
import proofs.RandomViability.BoundedCountModel

namespace RandomViability
open Classical FiniteCopy RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section

def isBasalChannel {n : ℕ} : PhysicalCountChannel n → Prop
  | .inr (.inl _) => True
  | _ => False

def boundedBasalIntensity {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) : ℝ :=
  ∑ ch, if isBasalChannel ch then (boundedPhysicalCountModel c V D basal cat).rate N ch else 0

theorem bounded_basal_rate_decomposition {n B : ℕ} (c : SourceMoleculeFibreConfig n)
    (V D : NNReal) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (ch : PhysicalCountChannel n) :
    (boundedPhysicalCountModel c V D basal cat).rate N ch =
      (boundedPhysicalCountModel c V D (fun _ => 0) cat).rate N ch +
        (if isBasalChannel ch then (boundedPhysicalCountModel c V D basal cat).rate N ch else 0) := by
  rcases ch with ((f | z) | (⟨r,d⟩ | ⟨r,z,d⟩)) <;>
    simp [boundedPhysicalCountModel, physicalChannelRate, physicalChannelCoefficient, isBasalChannel]

theorem bounded_basal_total_decomposition {n B : ℕ} (c : SourceMoleculeFibreConfig n)
    (V D : NNReal) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) :
    (boundedPhysicalCountModel c V D basal cat).total N =
      (boundedPhysicalCountModel c V D (fun _ => 0) cat).total N + boundedBasalIntensity c V D basal cat N := by
  unfold FiniteJumpModel.total boundedBasalIntensity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ch _
  exact bounded_basal_rate_decomposition c V D basal cat N ch

def nonBasalLabel {n : ℕ} : Option (PhysicalCountChannel n) → Prop
  | none => True
  | some ch => ¬ isBasalChannel ch

theorem bounded_basal_quiet_event_lower {n B : ℕ} (c : SourceMoleculeFibreConfig n)
    (V D : NNReal) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q0 q1 : NNReal) (h0 : 0 < (q0 : ℝ)) (h1 : 0 < (q1 : ℝ))
    (hb0 : ∀ N : BoundedCounts n B, (boundedPhysicalCountModel c V D (fun _ => 0) cat).total N ≤ q0)
    (hb1 : ∀ N : BoundedCounts n B, (boundedPhysicalCountModel c V D basal cat).total N ≤ q1)
    (hbasal : ∀ N : BoundedCounts n B, boundedBasalIntensity c V D basal cat N ≤ (q1 : ℝ)-q0)
    (t : NNReal) (N : BoundedCounts n B)
    (E : (m : ℕ) → RewardPath (Option (PhysicalCountChannel n)) m → Prop) :
    Real.exp (-(((q1 : ℝ)-q0)*t)) *
      (labeledUniformize (boundedPhysicalCountModel c V D (fun _ => 0) cat) q0 h0 hb0).poissonEventMass (q0*t) N E ≤
        (labeledUniformize (boundedPhysicalCountModel c V D basal cat) q1 h1 hb1).poissonEventMass (q1*t) N
          (fun m p => E m p ∧ FiniteLabeledKernel.pathAllowed nonBasalLabel m p) := by
  apply jump_quiet_allowed_event_lower _ _ q0 q1 h0 h1 hb0 hb1
  · intro x ch
    rfl
  · intro x ch
    rw [bounded_basal_rate_decomposition c V D basal cat x ch]
    have hp : 0 ≤ (if isBasalChannel ch then (boundedPhysicalCountModel c V D basal cat).rate x ch else 0) := by
      split_ifs
      · exact (boundedPhysicalCountModel c V D basal cat).nonneg x ch
      · exact le_rfl
    linarith
  · intro x
    rw [bounded_basal_total_decomposition]
    exact add_le_add (le_refl _) (hbasal x)
  · intro x ch h
    cases ch with
    | none => exact False.elim (h trivial)
    | some ch =>
      rcases ch with ((f | z) | (⟨r,d⟩ | ⟨r,z,d⟩))
      · exact False.elim (h (by simp [nonBasalLabel, isBasalChannel]))
      · exact False.elim (h (by simp [nonBasalLabel, isBasalChannel]))
      · simp [labeledUniformize, boundedPhysicalCountModel, physicalChannelRate, physicalChannelCoefficient]
      · exact False.elim (h (by simp [nonBasalLabel, isBasalChannel]))

end
end RandomViability

