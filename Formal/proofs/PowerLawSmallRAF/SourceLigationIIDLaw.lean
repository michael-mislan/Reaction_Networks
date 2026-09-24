import proofs.PowerLawSmallRAF.BernoulliBitProjection
import proofs.PowerLawSmallRAF.LigationRawCoordinates
import proofs.PowerLawSmallRAF.LigationSourceProjection

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 100000

def sourceLigationRawCoordinate (n : Nat) (words : List LigationWord)
    (hb : ∀ w ∈ words, w.length ≤ n) (i : LigationRawCoordinate words) : Reaction n :=
  ligationCutReaction n (ligationRawCoordinateWord words i)
    (hb _ (ligationRawCoordinateWord_mem words i)) (ligationRawCoordinateCut words i)

theorem sourceLigationRawCoordinate_injective (n : Nat) (words : List LigationWord)
    (hb : ∀ w ∈ words, w.length ≤ n) (hnd : words.Nodup) :
    Function.Injective (sourceLigationRawCoordinate n words hb) := by
  intro i j h
  have he := ligationCutReaction_injective n _ _ _ _ _ _ h
  exact ligationRawCoordinate_ext words hnd i j he.1 he.2

def sourceLigationRawCoordinateEmbedding (n : Nat) (words : List LigationWord)
    (hb : ∀ w ∈ words, w.length ≤ n) (hnd : words.Nodup) : LigationRawCoordinate words ↪ Reaction n :=
  ⟨sourceLigationRawCoordinate n words hb, sourceLigationRawCoordinate_injective n words hb hnd⟩

theorem sourceLigationRawConfiguration_decode (n : Nat) (H : Finset (Reaction n))
    (words : List LigationWord) (hb : ∀ w ∈ words, w.length ≤ n) :
    sourceLigationRawConfiguration n H words hb = ligationRawDecode words
      (fun i => decide (sourceLigationRawCoordinate n words hb i ∈ H)) := by
  induction words with
  | nil => rfl
  | cons w rest ih =>
      apply Prod.ext
      · rfl
      · exact ih _

/-- Exact source iid law on the actual split coordinates of a duplicate-free
schedule. All other source channels are integrated out. -/
theorem sourceLigationRawConfiguration_expectation (p : ℝ) (n : Nat)
    (words : List LigationWord) (hb : ∀ w ∈ words, w.length ≤ n) (hnd : words.Nodup)
    (F : LigationRawConfiguration words → ℝ) :
    (∑ H : Finset (Reaction n), bernoulliSubsetRowWeight p H *
      F (sourceLigationRawConfiguration n H words hb)) =
      ∑ cfg : LigationRawConfiguration words, ligationRawWeight p words cfg * F cfg := by
  calc
    _ = ∑ H : Finset (Reaction n), bernoulliSubsetRowWeight p H *
        F (ligationRawDecode words (fun i => decide
          (sourceLigationRawCoordinateEmbedding n words hb hnd i ∈ H))) := by
      apply Finset.sum_congr rfl
      intro H _
      rw [sourceLigationRawConfiguration_decode]
      rfl
    _ = ∑ B : LigationRawCoordinate words → Bool,
        bernoulliFullRowWeight p B * F (ligationRawDecode words B) :=
      bernoulliSubset_embedding_expectation p (sourceLigationRawCoordinateEmbedding n words hb hnd)
        (fun B => F (ligationRawDecode words B))
    _ = _ := ligationRawDecode_expectation p words F

theorem sourceLigationTargetConfiguration_expectation (p : ℝ) (n : Nat)
    (w : LigationWord) (hn : w.length ≤ n)
    (F : LigationRawConfiguration (ligationSubstringSchedule w) → ℝ) :
    (∑ H : Finset (Reaction n), bernoulliSubsetRowWeight p H *
      F (sourceLigationTargetConfiguration n w hn H)) =
      ∑ cfg : LigationRawConfiguration (ligationSubstringSchedule w),
        ligationRawWeight p (ligationSubstringSchedule w) cfg * F cfg :=
  sourceLigationRawConfiguration_expectation p n (ligationSubstringSchedule w)
    (ligationSubstringSchedule_source_bounds n w hn) (ligationSubstringSchedule_nodup w) F

end
end PowerLawSmallRAF
