import proofs.RepeatedFunction.IntervalPath
import proofs.RepeatedFunction.FeedAccounts
import proofs.RandomViability.PhysicalOutputEvent

namespace RandomViability
open Classical Set RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 100000

/-- Readiness is measured stock, not the presence of a catalytic incidence.
Its continuation guarantee is proved under a source certificate separately. -/
def observedReady {n : ℕ} (V : NNReal) (N : Molecule n → ℕ) : Prop :=
  (countMass N : ℝ)/V ≤ 21/2 ∧
  ∃ q : Molecule n, molLength q = 4 ∧ (1/3000000000000000000 : ℝ) ≤ (N q : ℝ)/V

def windowOutputReady {n : ℕ} (V : NNReal) (a b : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  ∃ J K,prefixElapsed J (Preorder.frestrictLe J z) ≤ a ∧
    a < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z) ∧
    prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤ b ∧
    b < prefixElapsed (J+K+1) (Preorder.frestrictLe (J+K+1) z) ∧
    (1/10 : ℝ) < markedWindowReward (fun _ => exportReward V) z J K ∧
    observedReady V (z (J+K)).1

/-- Two natural export windows, actual measured endpoints and gross feed.
The initial state, coefficient marks and frozen environment belong to the law. -/
def twoWindowMission {n : ℕ} (V : NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  (∀ k,prefixElapsed k (Preorder.frestrictLe k z) ≤ 199 → (countMass (z k).1 : ℝ) ≤ 11*V) ∧
  windowOutputReady V 1 100 z ∧ windowOutputReady V 100 199 z ∧
  (∃ L,prefixElapsed L (Preorder.frestrictLe L z) ≤ 199 ∧
    199 < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z) ∧
    markedWindowReward (fun _ => grossFeedReward V) z 0 L ≤ 1195) ∧
  ∃ J,prefixElapsed J (Preorder.frestrictLe J z) ≤ 1 ∧
    1 < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z) ∧ observedReady V (z J).1

theorem two_window_implies_old_output {n : ℕ} (V : NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hz : twoWindowMission V z) : physicalOutputEvent V z := by
  obtain ⟨J,K,hj,hj',hk,hk',he,_⟩ := hz.2.1
  exact ⟨fun k hk => hz.1 k (by linarith only [hk]),J,K,hj,hj',hk,hk',he⟩

end
end RandomViability
