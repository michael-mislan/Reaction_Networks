import proofs.RAF1519.Refinement.CountNetwork
import proofs.RandomViability.JumpSupport
import proofs.RandomViability.JumpInitial
import proofs.RandomViability.JumpWaitingSupport

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators

abbrev MolecularState (n : ℕ) := (Fin n × Fin 7) → ℕ
abbrev CountChannel (n : ℕ) := (Fin n × LocalChannel) ⊕ (Fin n × Fin n × Fin 7)

instance countChannelMeasurable (n : ℕ) : MeasurableSpace (CountChannel n) := ⊤
instance countChannelSingletons (n : ℕ) : MeasurableSingletonClass (CountChannel n) :=
  ⟨fun _ => trivial⟩

def atNode {n : ℕ} (i : Fin n) (R : Reaction (Fin 7)) : Reaction (Fin n × Fin 7) :=
  ⟨fun p => if p.1=i then R.consume p.2 else 0,
   fun p => if p.1=i then R.produce p.2 else 0,R.coefficient⟩

/-- Directed exchange labels use the same coefficient for every species.
Symmetry is needed later for graph comparisons, not for defining this law. -/
def graphReaction {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ) :
    CountChannel n → Reaction (Fin n × Fin 7)
  | .inl (i,j) => atNode i (localReaction (r i) (d i) j)
  | .inr (i,j,s) => ⟨Pi.single (i,s) 1,Pi.single (j,s) 1,k i j⟩

def molecularNext {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (N : MolecularState n) (a : CountChannel n) : MolecularState n :=
  (graphReaction r d k a).next N

def molecularRate {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (V : ℝ)
    (N : MolecularState n) (a : CountChannel n) : ℝ := (graphReaction r d k a).rate V N

theorem molecular_rate_nonnegative {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 ≤ V) (N : MolecularState n) (a : CountChannel n) :
    0 ≤ molecularRate r d k V N a := by
  apply Reaction.rate_nonnegative _ V hV
  rcases a with ⟨i,j⟩ | ⟨i,j,s⟩
  · exact local_coefficient_nonnegative (r i) (d i) (hr i) (hd i) j
  · exact hk i j

theorem food_rate {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (V : ℝ)
    (N : MolecularState n) (i : Fin n) (j : Fin 2) :
    molecularRate r d k V N (.inl (i,.inr (.inl j))) = V := by
  simp [molecularRate,graphReaction,atNode,localReaction,Reaction.rate]

theorem molecular_total_positive {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (N : MolecularState n) :
    0 < ∑ a, molecularRate r d k V N a := by
  let a : CountChannel n := .inl (⟨0,hn⟩,.inr (.inl 0))
  have ha : molecularRate r d k V N a = V := food_rate r d k V N ⟨0,hn⟩ 0
  have hb := Finset.single_le_sum
    (fun b _ => molecular_rate_nonnegative r d k V hr hd hk hV.le N b) (Finset.mem_univ a)
  rw [ha] at hb
  exact hV.trans_le hb

/-- Unrestricted chronological marked reaction law. No successful event is conditioned on. -/
def molecularLaw {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (N : MolecularState n) :
    Measure (ℕ → JumpState (MolecularState n) (CountChannel n)) :=
  jumpTrajectoryLaw N (molecularNext r d k) (molecularRate r d k V)
    (molecular_rate_nonnegative r d k V hr hd hk hV.le)
    (molecular_total_positive hn r d k V hr hd hk hV)

instance molecularLaw_probability {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (N : MolecularState n) :
    IsProbabilityMeasure (molecularLaw hn r d k V hr hd hk hV N) := by
  unfold molecularLaw
  infer_instance

end
end RAF1519.Refinement
