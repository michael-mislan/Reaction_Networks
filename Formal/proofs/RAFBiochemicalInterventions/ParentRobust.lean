import proofs.RAFBiochemicalInterventions.ParentIntervention
import proofs.RAFBiochemicalInterventions.SmallSource
import proofs.RAFBiochemicalInterventions.RobustBarrier

namespace RAFBiochemicalLiteral.ParentRobust
open ParentSource
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

theorem siphon : Siphon (remaining rows cut) blocked :=
  checked_siphon rows food blocked cut ParentSource.barrier_checked

theorem restorations (a : Nat) (ha : a ∈ cut) :
    Capable (remaining rows (restore cut a)) food target := by
  simp only [cut, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h
  · subst a; exact ParentIntervention.restoredR01209
  · subst a; exact ParentIntervention.restoredR01210
  · subst a; exact ParentIntervention.restoredR04441

theorem annotation_independent (F' : List Nat) (c : Nat → Formula)
    (hf : ∀ x ∈ F', x ∉ blocked) :
    ¬ Capable (remaining (rows.map (annotate c)) cut) F' target := by
  apply not_capable_of_not_generated
  rw [remaining_annotate]
  intro h
  exact siphon_food_independent _ blocked F' (siphon_annotate _ blocked c siphon) hf target h
    (by decide +kernel)

theorem robust_selective_minimal (F' : List Nat) (c : Nat → Formula)
    (hf : ∀ x ∈ food, x ∈ F') (havoid : ∀ x ∈ F', x ∉ blocked)
    (hw : Weakens rows c) :
    MinimalCut (rows.map (annotate c)) F' target cut ∧
    Capable (remaining (rows.map (annotate c)) cut) F' 68 := by
  constructor
  · exact robust_minimal rows food F' blocked cut c target siphon (by decide +kernel)
      hf havoid hw restorations
  · rw [remaining_annotate]
    apply capable_enlarge _ food F' c 68 hf ?_ ParentIntervention.methionine_preserved
    intro r hr
    exact hw r (List.mem_filter.mp hr).1

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
def rescueFood : List Nat := 132 :: food
def rescueSupport : List Row := [SmallSource.r7, SmallSource.r8, SmallSource.r4, SmallSource.r5]
theorem rescue_checked : checkSupport (remaining rows cut) rescueFood
    rescueSupport rescueSupport target = true := by decide +kernel
theorem precursor_rescue : Capable (remaining rows cut) rescueFood target :=
  checked_support _ _ _ _ _ rescue_checked

theorem firing_exclusion (X Y : List Nat) (hx : ∀ x ∈ X, x ∉ blocked)
    (h : FiringTrace (remaining rows cut) X Y) : ∀ y ∈ Y, y ∉ blocked :=
  firing_invariant _ blocked X Y siphon hx h

end RAFBiochemicalLiteral.ParentRobust
