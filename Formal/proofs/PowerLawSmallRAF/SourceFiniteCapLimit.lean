import proofs.PowerLawSmallRAF.SourceCriticalPatterns
import proofs.PowerLawSmallRAF.FiniteSeedMarginal

namespace PowerLawSmallRAF
open Classical Filter Topology MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete unitInterval
noncomputable section

theorem finiteMarkedPatternWeight_eq_atom {J Ω : Type*} [Fintype J] [DecidableEq J]
    [Fintype Ω] [DecidableEq Ω] (S : Finset J)
    (miss : J → Finset Ω) (w : Ω → ℝ) :
    finiteMarkedPatternWeight S (Finset.univ \ S) miss w =
      ∑ ω : Ω, if Finset.univ.filter (fun i => ω ∉ miss i) = S then w ω else 0 := by
  rw [finiteMarkedPatternWeight,allCoveredWeight,← Finset.sum_filter]
  have he : (S.inf (fun i => (miss i)ᶜ)).filter
      (fun ω => ω ∈ (Finset.univ \ S).inf miss) =
      Finset.univ.filter (fun ω => Finset.univ.filter (fun i => ω ∉ miss i) = S) := by
    ext ω
    simp only [Finset.mem_filter,Finset.mem_inf,Finset.mem_compl,
      Finset.mem_sdiff,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨hs,hc⟩
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro hi
        by_contra hn
        exact hi (hc i hn)
      · exact hs i
    · intro he
      have hi (i : J) : (ω ∉ miss i) ↔ i ∈ S := by
        rw [← he]
        simp
      exact ⟨fun i h => (hi i).mpr h, fun i h => by
        by_contra hn
        exact h ((hi i).mp hn)⟩
  rw [he,Finset.sum_filter]

def sourceFiniteCapBlock (N n : Nat) (r : Reaction N) : Finset (Reaction n) :=
  if h : N ≤ n then {sourceLiftSeedReaction N n h r} else ∅

def sourceFiniteCapOpen (N n : Nat) (config : SourceMoleculeFibreConfig n) :
    Finset (Reaction N) :=
  Finset.univ.filter (fun r => config ∉ sourceIndexedBlockMissEvent (sourceFiniteCapBlock N n) r)

theorem sourceFiniteCapOpen_eq_projection (N n : Nat) (hNn : N ≤ n)
    (config : SourceMoleculeFibreConfig n) :
    sourceFiniteCapOpen N n config =
      sourceSeedProjection n N hNn (Finset.univ.biUnion config) := by
  ext r
  simp [sourceFiniteCapOpen,sourceFiniteCapBlock,hNn,sourceIndexedBlockMissEvent,
    sourceSeedProjection,Finset.disjoint_singleton_right]

theorem sourceFiniteCapBlock_card (N : Nat) :
    ∀ᶠ n : Nat in atTop, ∀ T : Finset (Reaction N),
      (T.biUnion (sourceFiniteCapBlock N n)).card = T.card := by
  filter_upwards [eventually_ge_atTop N] with n hn T
  have he : T.biUnion (sourceFiniteCapBlock N n) =
      T.image (sourceLiftSeedReaction N n hn) := by
    ext r
    simp [sourceFiniteCapBlock,hn,eq_comm]
  rw [he]
  exact Finset.card_image_of_injective _ (sourceLiftSeedReaction_injective N n hn)

def sourceCriticalOpenness : I :=
  ⟨1-Real.exp (-criticalLambda (-2)),by
    constructor
    · have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (criticalLambda_pos (-2)).le)
      linarith
    · have h := Real.exp_pos (-criticalLambda (-2))
      linarith⟩

theorem sourceFiniteCap_atom_tendsto (N : Nat) (S : Finset (Reaction N)) :
    Tendsto (fun n : Nat => ∑ config : SourceMoleculeFibreConfig n,
      if sourceFiniteCapOpen N n config = S then
        sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0) atTop
      (𝓝 (bernoulliSubsetRowWeight (sourceCriticalOpenness : ℝ) S)) := by
  have ht := sourceExactCriticalDistinctPattern_tendsto S (Finset.univ \ S)
    disjoint_sdiff_self_right (sourceFiniteCapBlock N) (by
      filter_upwards [sourceFiniteCapBlock_card N] with n hn T _
      exact hn (T ∪ (Finset.univ \ S)))
  simp_rw [finiteMarkedPatternWeight_eq_atom] at ht
  have he : (1-Real.exp (-criticalLambda (-2)))^S.card *
      Real.exp (-(((Finset.univ \ S).card : ℝ)*criticalLambda (-2))) =
      bernoulliSubsetRowWeight (sourceCriticalOpenness : ℝ) S := by
    rw [bernoulliSubsetRowWeight]
    simp only [sourceCriticalOpenness, sub_sub_cancel]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at ht
  exact ht

theorem sourceFiniteCap_event_tendsto (N : Nat) (E : Finset (Reaction N) → Prop) :
    Tendsto (fun n : Nat => ∑ config : SourceMoleculeFibreConfig n,
      if E (sourceFiniteCapOpen N n config) then
        sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0) atTop
      (𝓝 ((staticReactionMeasure N sourceCriticalOpenness)
        {ω | E (staticOpenReactions ω)}).toReal) := by
  rw [staticReactionMeasure_subset_event]
  have ht : ∀ S ∈ (Finset.univ : Finset (Finset (Reaction N))), Tendsto (fun n : Nat =>
      if E S then ∑ config : SourceMoleculeFibreConfig n,
        if sourceFiniteCapOpen N n config = S then
          sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0 else 0) atTop
      (𝓝 (if E S then bernoulliSubsetRowWeight (sourceCriticalOpenness : ℝ) S else 0)) := by
    intro S _
    by_cases h : E S
    · simpa only [if_pos h] using sourceFiniteCap_atom_tendsto N S
    · simp only [if_neg h]
      exact tendsto_const_nhds
  apply (tendsto_finsetSum Finset.univ ht).congr'
  apply Filter.Eventually.of_forall
  intro n
  have hd (S : Finset (Reaction N)) :
      (if E S then ∑ config : SourceMoleculeFibreConfig n,
        if sourceFiniteCapOpen N n config = S then
          sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0 else 0) =
      ∑ config : SourceMoleculeFibreConfig n, if E S then
        if sourceFiniteCapOpen N n config = S then
          sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0 else 0 := by
    by_cases h : E S <;> simp [h]
  simp_rw [hd]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro config _
  have hp : ∀ S : Finset (Reaction N),
      (if E S then if sourceFiniteCapOpen N n config = S then
        sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0 else 0) =
      (if sourceFiniteCapOpen N n config = S then
        if E (sourceFiniteCapOpen N n config) then
          sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0 else 0) := by
    intro S
    by_cases h : sourceFiniteCapOpen N n config = S
    · simp [← h]
    · simp [h]
  simp_rw [hp]
  simp

end
end PowerLawSmallRAF
