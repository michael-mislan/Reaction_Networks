import proofs.PowerLawSmallRAF.FiniteSeedMarginal

namespace PowerLawSmallRAF
open Classical MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete unitInterval
noncomputable section

def sourceFiniteSeedEvent (n N m : Nat) (H : Finset (Reaction n)) : Prop :=
  ∀ w ∈ actualBinaryWords m, FiniteReversibleGenerated N 2 (sourceSeedField n H) w

def sourceFiniteSeedMass (a : ℝ) (n N m : Nat) : ℝ :=
  ∑ H : Finset (Reaction n), if sourceFiniteSeedEvent n N m H then bernoulliSubsetRowWeight a H else 0

/-- The exact finite seed event in the larger auxiliary field has the
finite static seed probability used by the survival approximation. -/
theorem sourceFiniteSeedMass_eq_static (n N m : Nat) (hNn : N ≤ n) (a : I) :
    sourceFiniteSeedMass (a : ℝ) n N m =
      (staticReactionMeasure N a {ω | ∀ w ∈ actualBinaryWords m,
        ∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions ω), moleculeWord x = w}).toReal := by
  classical
  have he (H : Finset (Reaction n)) : sourceFiniteSeedEvent n N m H ↔
      ∀ w ∈ actualBinaryWords m, ∃ x ∈ temporaryReactionClosure 2 (sourceSeedProjection n N hNn H),
        moleculeWord x = w := by
    unfold sourceFiniteSeedEvent
    apply forall_congr'
    intro w
    apply forall_congr'
    intro _
    rw [finiteReversible_iff_literalClosure,restrictedSplitReactions_sourceSeedProjection n N hNn H]
  unfold sourceFiniteSeedMass
  simp_rw [he]
  convert sourceSeedProjection_event_mass n N hNn a (fun H =>
    ∀ w ∈ actualBinaryWords m, ∃ x ∈ temporaryReactionClosure 2 H, moleculeWord x = w) using 1
  apply Finset.sum_congr rfl
  intro H _
  split_ifs <;> rfl

/-- The same fixed witness cap captures the prescribed iid survival mass
in every larger auxiliary horizon, with a uniform extension error. -/
theorem source_fixed_seed_uniform_survival_mass (a : I) (ha : 1/2 < (a : ℝ))
    (ε : ℝ) (hε : 0 < ε) (c : ENNReal) (hc : c < staticSurvival a) :
    ∃ m N : Nat, 2 ≤ m ∧ m ≤ N ∧
      (∀ n : Nat, N ≤ n → c.toReal < sourceFiniteSeedMass (a : ℝ) n N m) ∧
      (∀ n L : Nat, L ≤ n → sourceAboveSeedFailureMass (a : ℝ) n m L < ε) := by
  obtain ⟨m,N,hm,hNm,hseed,hext⟩ := fixed_seed_uniform_extension_bridge a ha ε hε c hc
  refine ⟨m,N,hm,hNm,?_,hext⟩
  intro n hNn
  rw [sourceFiniteSeedMass_eq_static n N m hNn a]
  exact (ENNReal.toReal_lt_toReal hseed.ne_top (measure_ne_top _ _)).mpr hseed

end
end PowerLawSmallRAF
