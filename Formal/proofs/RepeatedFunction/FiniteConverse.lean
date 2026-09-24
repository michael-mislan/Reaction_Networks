import proofs.RepeatedFunction.EnsembleBounds

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000
set_option maxRecDepth 4096
local instance converseChannelSpace (n : ℕ) : MeasurableSpace (PhysicalCountChannel n) := ⊤
local instance converseChannelSingleton (n : ℕ) : MeasurableSingletonClass (PhysicalCountChannel n) := ⟨fun _ => trivial⟩

theorem productive_incidence_implies_short_four {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (z : Molecule n) (r : Reaction n) (hp : ProductiveSingletonIncidence r z) (hs : r ∈ c z) :
    ShortIncidence 4 c := by
  have hlen : molLength (reactionLeft r)+molLength (reactionRight r) = molLength (reactionProduct r) := by
    simpa only [molLength_reactionLeft,molLength_reactionRight,molLength_reactionProduct] using reaction_length_add r
  have hleft := hp.1
  have hright := hp.2.1
  have hprod : molLength (reactionProduct r) ≤ 4 := by omega
  have hz : molLength z ≤ 4 := by
    rcases hp.2.2.2 with h | h
    · omega
    · simpa only [h] using hprod
  refine ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩,r,?_,hs⟩
  rw [← molLength_reactionProduct]
  omega

theorem source_union_mass_le {n : ℕ} (a : ℝ) (ha : 1 < a)
    (A B : SourceMoleculeFibreConfig n → Prop) :
    eventMass a n (fun c => A c ∨ B c) ≤ eventMass a n A+eventMass a n B := by
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c _
  have hw := sourcePowerLawConfigWeight_nonneg a n ha c
  by_cases hA : A c <;> by_cases hB : B c
  all_goals simp only [hA,hB,or_true,or_false,if_true,if_false]
  all_goals linarith only [hw]

/-- A small explicit short-incidence coefficient replaces the astronomical
coefficient in the original broad upper bound. The old local-multiplicity
remainder is retained, not declared numerically small. -/
theorem averaged_mission_finite_upper {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ)) (hsmall : (n : ℝ)/(V : ℝ) ≤ 1/200000)
    (a : ℝ) (ha : 1 < a) (A : SourceMoleculeFibreConfig n → Prop) :
    averagedMissionProbability hn V hV a A ≤
      (Fintype.card (Molecule 4)*Fintype.card (Reaction 6) : ℕ)*
        (windowZipfMean a (sourceReactionCount n)/sourceReactionCount n)+
      eventMass a n (fun c => ¬AtMostOneLocalIncidence singleIncidenceCutoff c)+
      localOutputNoiseUpper n (V : NNReal) := by
  apply (averaged_mission_le_output hn V hV a ha A).trans
  have hcard : (0 : ℝ) < Fintype.card (KineticMarkConfig n) := by exact_mod_cast Fintype.card_pos
  unfold averagedOutputProbability uniformFiniteAverage
  simp only [if_true]
  rw [div_le_iff₀ hcard]
  calc
    _ ≤ ∑ _u : KineticMarkConfig n,
        ((Fintype.card (Molecule 4)*Fintype.card (Reaction 6) : ℕ)*
        (windowZipfMean a (sourceReactionCount n)/sourceReactionCount n)+
        eventMass a n (fun c => ¬AtMostOneLocalIncidence singleIncidenceCutoff c)+
        localOutputNoiseUpper n (V : NNReal)) := by
      apply Finset.sum_le_sum
      intro u _
      have hbase := sourceAverage_le_bad_add a n ha hn
        (fun c => ShortIncidence 4 c ∨ ¬AtMostOneLocalIncidence singleIncidenceCutoff c)
        (fun c => if A c then (physicalTrajectoryLaw (by omega : 2 ≤ n) c (V : NNReal) 1
          (by exact_mod_cast hV) (by norm_num) (kineticBasal u) (kineticCatalytic u)
          (foodOnlyCounts n V) {z | physicalOutputEvent (V : NNReal) z}).toReal else 0)
        (localOutputNoiseUpper n (V : NNReal)) (by unfold localOutputNoiseUpper; positivity)
      apply le_trans (hbase ?_ ?_)
      · have hu := source_union_mass_le (n := n) a ha (ShortIncidence 4)
          (fun c => ¬AtMostOneLocalIncidence singleIncidenceCutoff c)
        exact add_le_add (hu.trans (add_le_add (shortIncidence_mass_le a n 4 ha hn) le_rfl)) le_rfl
      · intro c
        dsimp only
        split_ifs
        · exact measureReal_le_one
        · norm_num
      · intro c hg
        have hone : AtMostOneLocalIncidence singleIncidenceCutoff c := not_not.mp (not_or.mp hg).2
        have hno : noProductiveSingleton c := fun z r hs hp =>
          (not_or.mp hg).1 (productive_incidence_implies_short_four c z r hp hs)
        dsimp only
        split_ifs
        · exact physical_output_upper_at_most_one_local hn c hone hno (V : NNReal)
            (by exact_mod_cast hV) hscale hsmall (kineticBasal u) (kineticCatalytic u)
            (fun r => (kinetic_basal_bounds u r).2) (fun r z => (kinetic_catalytic_bounds u r z).2)
            (foodOnlyCounts n V) (food_only_nonfood_zero n V)
        · unfold localOutputNoiseUpper
          positivity
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end
end RandomViability
