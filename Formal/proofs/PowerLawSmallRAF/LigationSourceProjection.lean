import proofs.PowerLawSmallRAF.LigationSourceClosure
import proofs.PowerLawSmallRAF.FiniteLigationTarget

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
noncomputable section
set_option maxHeartbeats 100000

/-- Read the actual indexed channel marks, reusing the same mark whenever
the same word and split occur again. -/
def sourceLigationRawConfiguration (n : Nat) (H : Finset (Reaction n)) :
    (words : List LigationWord) → (∀ w ∈ words, w.length ≤ n) → LigationRawConfiguration words
  | [], _ => ()
  | w :: rest, hb =>
      (fun i => decide (ligationCutReaction n w (hb w (List.mem_cons_self ..)) i ∈ H),
        sourceLigationRawConfiguration n H rest (fun u hu => hb u (List.mem_cons_of_mem w hu)))

theorem sourceLigationRawConfiguration_supported (n : Nat) (H T : Finset (Reaction n))
    (hHT : H ⊆ T) (words : List LigationWord) (hb : ∀ w ∈ words, w.length ≤ n) :
    SourceLigationRawSupported n T words (sourceLigationRawConfiguration n H words hb) := by
  induction words with
  | nil => trivial
  | cons w rest ih =>
      constructor
      · intro i hi
        refine ⟨hb w (List.mem_cons_self ..), hHT ?_⟩
        exact of_decide_eq_true hi
      · exact ih _

theorem sourceLigationRawConfiguration_generated (n : Nat) (H T : Finset (Reaction n))
    (hHT : H ⊆ T) (words : List LigationWord) (hb : ∀ w ∈ words, w.length ≤ n)
    (known : Finset LigationWord) (hk : ∀ u ∈ known, SourceLigationGenerated n T u) :
    ∀ u ∈ ligationRawKnown words (sourceLigationRawConfiguration n H words hb) known,
      SourceLigationGenerated n T u :=
  ligationRawKnown_source_generated n T words _ known
    (sourceLigationRawConfiguration_supported n H T hHT words hb) hk

theorem ligationSubstringSchedule_source_bounds (n : Nat) (w : LigationWord) (hn : w.length ≤ n) :
    ∀ u ∈ ligationSubstringSchedule w, u.length ≤ n := by
  intro u hu
  have hs : u ∈ ligationSubstrings w := by
    rw [← ligationSubstringSchedule_toFinset]
    exact List.mem_toFinset.mpr hu
  exact ((mem_ligationSubstrings_iff w u).mp hs).1.length_le.trans hn

def sourceLigationTargetConfiguration (n : Nat) (w : LigationWord) (hn : w.length ≤ n)
    (H : Finset (Reaction n)) : LigationRawConfiguration (ligationSubstringSchedule w) :=
  sourceLigationRawConfiguration n H (ligationSubstringSchedule w)
    (ligationSubstringSchedule_source_bounds n w hn)

/-- With a genuinely generated nucleus, concrete target failure forces raw
target failure. Additional production channels in T may help, never hurt. -/
theorem sourceLigationTarget_failure_inclusion (n L : Nat) (w : LigationWord)
    (hn : w.length ≤ n) (H T : Finset (Reaction n)) (hHT : H ⊆ T)
    (hnucleus : ∀ u ∈ ligationTargetNucleus L w, SourceLigationGenerated n T u)
    (hfail : ¬ SourceLigationGenerated n T w) :
    w ∉ ligationRawKnown (ligationSubstringSchedule w)
      (sourceLigationTargetConfiguration n w hn H) (ligationTargetNucleus L w) := by
  intro hw
  exact hfail (sourceLigationRawConfiguration_generated n H T hHT
    (ligationSubstringSchedule w) (ligationSubstringSchedule_source_bounds n w hn)
    (ligationTargetNucleus L w) hnucleus w hw)

end
end PowerLawSmallRAF
