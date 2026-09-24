import proofs.CompositionalMemory.FrozenCountTrajectory
import proofs.CompositionalMemory.ImmediateCopyNecessity

namespace CompositionalMemory
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopy HeritableCompositions
noncomputable section
local instance {β : Type*} : MeasurableSpace (Option β) := ⊤
local instance {β : Type*} : MeasurableSingletonClass (Option β) := ⟨fun _ => trivial⟩

def firstHitPredicate {α : Type*} (D : Set α) (z : ℕ → α) (j : ℕ) : Prop :=
  if ∃ i, z i ∈ D then z j ∈ D else j=0

theorem firstHit_exists {α : Type*} (D : Set α) (z : ℕ → α) :
    ∃ j, firstHitPredicate D z j := by
  by_cases h : ∃ i,z i ∈ D
  · simp [firstHitPredicate,h]
  · exact ⟨0,by simp [firstHitPredicate,h]⟩

def firstHitIndex {α : Type*} (D : Set α) (z : ℕ → α) : ℕ :=
  Nat.find (firstHit_exists D z)

theorem firstHit_spec {α : Type*} (D : Set α) (z : ℕ → α) (h : ∃ i,z i ∈ D) :
    z (firstHitIndex D z) ∈ D ∧ ∀ j < firstHitIndex D z,z j ∉ D := by
  constructor
  · simpa [firstHitPredicate,h] using Nat.find_spec (firstHit_exists D z)
  · intro j hj hh
    exact Nat.find_min (firstHit_exists D z) hj (by simpa [firstHitPredicate,h] using hh)

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

theorem firstHitIndex_measurable (D : Set α) : Measurable (firstHitIndex D) := by
  have he : MeasurableSet {z : ℕ → α | ∃ i,z i ∈ D} := by
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion (fun i => ((Set.to_countable D).measurableSet.preimage (measurable_pi_apply i)))
  apply measurable_find
  intro j
  have hj : MeasurableSet {z : ℕ → α | z j ∈ D} :=
    (Set.to_countable D).measurableSet.preimage (measurable_pi_apply j)
  change MeasurableSet {z : ℕ → α | if ∃ i,z i ∈ D then z j ∈ D else j=0}
  convert (he.inter hj).union (he.compl.inter (MeasurableSet.const (j=0))) using 1
  ext z
  by_cases h : ∃ i,z i ∈ D <;> simp [h]

def firstHitObservation {β : Type*} (D : Set α) (project : α → Option β) (z : ℕ → α) : Option β :=
  if ∃ i,z i ∈ D then project (z (firstHitIndex D z)) else none

theorem firstHitObservation_measurable {β : Type*}
    (D : Set α) (project : α → Option β) : Measurable (firstHitObservation D project) := by
  have he : MeasurableSet {z : ℕ → α | ∃ i,z i ∈ D} := by
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion (fun i => ((Set.to_countable D).measurableSet.preimage (measurable_pi_apply i)))
  have hev : Measurable (fun p : (ℕ → α) × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left (fun j => measurable_pi_apply j)
  exact Measurable.ite he ((measurable_of_countable project).comp
    (hev.comp (measurable_id.prodMk (firstHitIndex_measurable D)))) measurable_const

def measureFiniteLaw {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure β) [IsProbabilityMeasure μ] : FiniteLaw β := {
  mass := fun b => (μ {b}).toReal
  nonneg := fun _ => ENNReal.toReal_nonneg
  total := by simpa [Measure.real, measure_univ] using
    (sum_measureReal_singleton (μ := μ) (s := Finset.univ)) }

abbrev CappedParent (k N : ℕ) := Fin k → Fin 4 → Fin (280*N+1)

def projectParent {k : ℕ} (N : ℕ) (n : Fin k → Counts) : Option (CappedParent k N) :=
  if h : ∀ i a,n i a ≤ 280*N then some (fun i a => ⟨n i a,by have := h i a; omega⟩) else none

def cappedCounts {k N : ℕ} (p : CappedParent k N) : Fin k → Counts := fun i a => (p i a).val

theorem project_parent_preserves_return {k : ℕ} (N : ℕ) (σ : Fin k → Bool)
    (n : Fin k → Counts) (d : WordDraw k) (hd : d ∈ wordDraws n)
    (h : closedWordReturn N σ n d) :
    ∃ p, projectParent N n=some p ∧ cappedCounts p=n := by
  have hc := closed_return_parent_cap N σ n d hd h
  have hb : ∀ i a,n i a ≤ 280*N := fun i a =>
    (Finset.single_le_sum (fun b _ => Nat.zero_le (n i b)) (Finset.mem_univ a)).trans (hc i)
  refine ⟨fun i a => ⟨n i a,by have := hb i a; omega⟩,?_,rfl⟩
  simp [projectParent,hb]

def sourceFirstParent {k : ℕ} (N : ℕ) (z : ℕ → JumpState (ModularCountState k) (FrozenCountChannel k)) :
    Option (CappedParent k N) :=
  firstHitObservation {s : ModularCountState k | s.2=2*(k*N)}
    (fun s => projectParent N s.1) (fun j => (z j).1)

theorem sourceFirstParent_measurable {k : ℕ} (N : ℕ) : Measurable (@sourceFirstParent k N) :=
  (firstHitObservation_measurable _ _).comp (measurable_pi_lambda _ (fun j => (measurable_pi_apply j).fst))

def sourceFirstParentLaw {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j,0 ≤ w i j) (N : ℕ) (s : ModularCountState k) :
    FiniteLaw (Option (CappedParent k N)) := by
  haveI : IsProbabilityMeasure (frozenCountTrajectory γ w hγ hw N s) := by
    unfold frozenCountTrajectory
    infer_instance
  let μ := (frozenCountTrajectory γ w hγ hw N s).map (sourceFirstParent N)
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (sourceFirstParent_measurable N).aemeasurable
  exact measureFiniteLaw μ

def immediateFromParent {k : ℕ} (N : ℕ) (σ : Fin k → Bool) :
    Option (CappedParent k N) → FiniteLaw (WordBirthOutcome N (sourceWordCenter σ) σ)
  | none => FiniteLaw.pure none
  | some p => immediateWordPartitionLaw N σ (cappedCounts p)

def sourceImmediateLaw {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j,0 ≤ w i j) (N : ℕ) (σ : Fin k → Bool)
    (n : WordBirthCount N (sourceWordCenter σ) σ) :=
  (sourceFirstParentLaw γ w hγ hw N (n.val,k*N)).bind (immediateFromParent N σ)

theorem source_immediate_failure_lower {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j,0 ≤ w i j) (N : ℕ) (hN : 1 ≤ N) (σ : Fin k → Bool)
    (n : WordBirthCount N (sourceWordCenter σ) σ) :
    1-necessitySurvival k N ≤ (sourceImmediateLaw γ w hγ hw N σ n).mass none := by
  apply finite_bind_failure_lower
  intro p
  cases p with
  | none => simpa [immediateFromParent,FiniteLaw.pure] using
      (sub_le_self 1 (necessitySurvival_nonneg k N))
  | some p => exact immediate_partition_failure N hN σ (cappedCounts p)

theorem source_immediate_lineage_upper {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j,0 ≤ w i j) (N : ℕ) (hN : 1 ≤ N) (σ : Fin k → Bool)
    (G : ℕ) (n : WordBirthCount N (sourceWordCenter σ) σ) :
    wordLineageSuccess (sourceImmediateLaw γ w hγ hw N σ) G n ≤
      (1-(1/2 : ℝ)^(280*N))^(k*G) := by
  have h := word_lineage_upper _ (necessitySurvival k N) (necessitySurvival_nonneg k N)
    (source_immediate_failure_lower γ w hγ hw N hN σ) G n
  simpa only [necessitySurvival,← pow_mul] using h

end
end CompositionalMemory
