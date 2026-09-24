import proofs.PowerLawSmallRAF.FiniteSeedNucleusSelection
import proofs.PowerLawSmallRAF.StaticSubsetProbability

namespace PowerLawSmallRAF
open Classical MeasureTheory ProbabilityTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete unitInterval
noncomputable section

theorem sourceLiftSeedReaction_injective (N n : Nat) (hNn : N ≤ n) :
    Function.Injective (sourceLiftSeedReaction N n hNn) := by
  intro r s h
  rcases r with ⟨⟨k,hk⟩,p⟩
  rcases s with ⟨⟨l,hl⟩,q⟩
  have hkl : k = l := congrArg (fun r : Reaction n => r.1.val) h
  subst l
  have hp : p = q := by simpa [sourceLiftSeedReaction] using h
  subst q
  rfl

theorem literalSplitCoordinate_lift (N n : Nat) (hNn : N ≤ n) (r : Reaction N) :
    literalSplitCoordinate (sourceLiftSeedReaction N n hNn r) = literalSplitCoordinate r := by
  rfl

def sourceSeedProjection (n N : Nat) (hNn : N ≤ n) (H : Finset (Reaction n)) :
    Finset (Reaction N) := Finset.univ.filter (fun r => sourceLiftSeedReaction N n hNn r ∈ H)

theorem restrictedSplitReactions_sourceSeedProjection (n N : Nat) (hNn : N ≤ n)
    (H : Finset (Reaction n)) :
    restrictedSplitReactions N (sourceSeedField n H) = sourceSeedProjection n N hNn H := by
  classical
  ext r
  simp only [restrictedSplitReactions,sourceSeedProjection,Finset.mem_filter,
    Finset.mem_univ,true_and,sourceSeedField]
  constructor
  · rintro ⟨s,hs,he⟩
    have he' : literalSplitCoordinate s = literalSplitCoordinate (sourceLiftSeedReaction N n hNn r) := he
    exact (literalSplitCoordinate_injective n he') ▸ hs
  · intro hr
    exact ⟨sourceLiftSeedReaction N n hNn r,hr,rfl⟩

theorem staticReactionMeasure_cap_map (n N : Nat) (hNn : N ≤ n) (a : I) :
    (staticReactionMeasure n a).map (fun ω r => ω (sourceLiftSeedReaction N n hNn r)) =
      staticReactionMeasure N a := by
  have hi := (staticReactionMeasure_indep n a).precomp (sourceLiftSeedReaction_injective N n hNn)
  rw [hi.map_fun_eq_pi_map (fun r => (measurable_pi_apply (sourceLiftSeedReaction N n hNn r)).aemeasurable)]
  have he (r : Reaction N) :
      (staticReactionMeasure n a).map (fun ω => ω (sourceLiftSeedReaction N n hNn r)) = ambientCoordLaw a := by
    rw [staticReactionMeasure,Measure.infinitePi_map_eval]
  simp_rw [he]
  exact (Measure.infinitePi_eq_pi _).symm

/-- All finite-cap events retain exactly their iid mass in the larger
auxiliary field. This is a finite marginal statement, not a Zipf limit. -/
theorem sourceSeedProjection_event_mass (n N : Nat) (hNn : N ≤ n) (a : I)
    (E : Finset (Reaction N) → Prop) :
    (∑ H : Finset (Reaction n), if E (sourceSeedProjection n N hNn H)
      then bernoulliSubsetRowWeight (a : ℝ) H else 0) =
    (staticReactionMeasure N a {ω | E (staticOpenReactions ω)}).toReal := by
  classical
  rw [← staticReactionMeasure_subset_event]
  rw [← staticReactionMeasure_cap_map n N hNn a,
    Measure.map_apply (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))
      (Set.Finite.measurableSet (Set.toFinite _))]
  congr 2
  ext ω
  have he : sourceSeedProjection n N hNn (staticOpenReactions ω) =
      staticOpenReactions (fun r => ω (sourceLiftSeedReaction N n hNn r)) := by
    ext r
    simp [sourceSeedProjection,staticOpenReactions]
  simp only [Set.mem_preimage,Set.mem_setOf_eq,he]

end
end PowerLawSmallRAF
