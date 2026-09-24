import proofs.HordijkSteelThreshold.ReversiblePoolCore

namespace HordijkSteelThreshold

open Filter MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- All molecules generated at some finite stage by the exact reversible
seeded maxRAF.  The ambient molecule type is finite, but keeping the stage
existential makes the definition coincide literally with food closure. -/
noncomputable def seededClosureMolecules {n : Nat}
    (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) : Finset (Molecule n) := by
  classical
  exact Finset.univ.filter fun x => ∃ k,
    x ∈ revClosureAt (binaryPolymerCRS n 2) (gatewaySeededMaxRAF bulk J) k

@[simp] theorem mem_seededClosureMolecules {n : Nat}
    (bulk : Set (NonseedCoord n)) (J : Finset (PolymerSeedReaction n 2))
    (x : Molecule n) :
    x ∈ seededClosureMolecules bulk J ↔ ∃ k,
      x ∈ revClosureAt (binaryPolymerCRS n 2)
        (gatewaySeededMaxRAF bulk J) k := by
  classical
  simp [seededClosureMolecules]

/-- Macroscopic seeded-bulk ignition means that the exact reversible cavity
closure contains at least half of the molecule universe. -/
def SeededBulkMacroEvent (n : Nat)
    (J : Finset (PolymerSeedReaction n 2)) :
    Set (Set (NonseedCoord n)) :=
  {bulk | Fintype.card (Molecule n) ≤
    2 * (seededClosureMolecules bulk J).card}

@[simp] theorem mem_SeededBulkMacroEvent {n : Nat}
    (J : Finset (PolymerSeedReaction n 2)) (bulk : Set (NonseedCoord n)) :
    bulk ∈ SeededBulkMacroEvent n J ↔
      Fintype.card (Molecule n) ≤
        2 * (seededClosureMolecules bulk J).card := by
  rfl

/-- Exact finite-size macroscopic ignition probability after fixing the
gateway trace and sampling only nongateway catalysis coordinates. -/
noncomputable def seededBulkMacroProbability (n : Nat) (lambda : ℝ)
    (J : Finset (PolymerSeedReaction n 2)) : ℝ :=
  ENNReal.toReal <| setBernoulli (Set.univ : Set (NonseedCoord n))
    (catalysisP n lambda) (SeededBulkMacroEvent n J)

/-- A positive seeded macroscopic phase is present when its exact finite-size
probability is eventually bounded away from zero. -/
def HasPositiveSeededBulkPhase
    (J : ∀ n, Finset (PolymerSeedReaction n 2)) (lambda : ℝ) : Prop :=
  ∃ epsilon : ℝ, 0 < epsilon ∧
    ∀ᶠ n in atTop, epsilon ≤ seededBulkMacroProbability n lambda (J n)

/-- Candidate lower critical intensity for a prescribed finite gateway trace
sequence in the exact reversible seeded-bulk model. -/
noncomputable def seededBulkCritical
    (J : ∀ n, Finset (PolymerSeedReaction n 2)) : ℝ :=
  sInf {lambda : ℝ | 0 < lambda ∧ HasPositiveSeededBulkPhase J lambda}

theorem hasPositiveSeededBulkPhase_iff
    (J : ∀ n, Finset (PolymerSeedReaction n 2)) (lambda : ℝ) :
    HasPositiveSeededBulkPhase J lambda ↔
      ∃ epsilon : ℝ, 0 < epsilon ∧
        ∀ᶠ n in atTop,
          epsilon ≤ seededBulkMacroProbability n lambda (J n) := by
  rfl

end HordijkSteelThreshold
