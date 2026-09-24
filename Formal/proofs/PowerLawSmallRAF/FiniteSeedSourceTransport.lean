import proofs.PowerLawSmallRAF.FixedSeedExtensionBridge

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete HordijkSteelThreshold
noncomputable section

theorem ligationWordCode_eq_binaryWordCode (w : LigationWord) :
    ligationWordCode w = binaryWordCode w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [ligationWordCode,binaryWordCode,ih]

theorem sourceOwnerWord_eq_moleculeWord {n : Nat} (x : Molecule n) :
    sourceOwnerWord x = moleculeWord x := by
  apply ligationWordCode_injective_of_length
  · rw [sourceOwnerWord_length,moleculeWord_length]
  · rw [sourceOwnerWord_code,ligationWordCode_eq_binaryWordCode,binaryWordCode_moleculeWord]

def sourceSeedField (n : Nat) (H : Finset (Reaction n)) : InfiniteSplitEnvironment :=
  fun w k => ∃ r ∈ H, literalSplitCoordinate r = (w,k)

theorem restrictedSplitReactions_sourceSeedField (n : Nat) (H : Finset (Reaction n)) :
    restrictedSplitReactions n (sourceSeedField n H) = H := by
  classical
  ext r
  simp only [restrictedSplitReactions,Finset.mem_filter,Finset.mem_univ,true_and,sourceSeedField]
  constructor
  · rintro ⟨s,hs,he⟩
    have hr : s = r := literalSplitCoordinate_injective n he
    simpa only [hr] using hs
  · intro hr
    exact ⟨r,hr,rfl⟩

def cappedSeedField (N : Nat) (field : InfiniteSplitEnvironment) : InfiniteSplitEnvironment :=
  fun w k => w.length ≤ N ∧ field w k

theorem finiteReversibleGenerated_capped {N L : Nat} {field : InfiniteSplitEnvironment}
    {w : List Bool} (h : FiniteReversibleGenerated N L field w) :
    FiniteReversibleGenerated N L (cappedSeedField N field) w := by
  induction h with
  | food hne hL hN => exact .food hne hL hN
  | ligate _ _ ho hN ihu ihv => exact .ligate ihu ihv ⟨hN,ho⟩ hN
  | left hu hv hp ho ih => exact .left hu hv ih ⟨finiteReversibleGenerated_length_le hp,ho⟩
  | right hu hv hp ho ih => exact .right hu hv ih ⟨finiteReversibleGenerated_length_le hp,ho⟩

def sourceSeedRestriction (n N : Nat) (H : Finset (Reaction n)) : Finset (Reaction n) :=
  H.filter (fun r => reactionProductLength r ≤ N)

theorem restrictedSplitReactions_capped_sourceSeedField (n N : Nat) (H : Finset (Reaction n)) :
    restrictedSplitReactions n (cappedSeedField N (sourceSeedField n H)) = sourceSeedRestriction n N H := by
  classical
  ext r
  have hh := Finset.ext_iff.mp (restrictedSplitReactions_sourceSeedField n H) r
  simp only [restrictedSplitReactions,Finset.mem_filter,Finset.mem_univ,true_and] at hh
  simp only [restrictedSplitReactions,sourceSeedRestriction,Finset.mem_filter,Finset.mem_univ,
    true_and,cappedSeedField,moleculeWord_length,molLength_reactionProduct,hh,and_comm]

/-- The whole finite witness cap is retained, including longer products
needed for reverse cleavage. No larger-horizon channels enter the base. -/
theorem source_finite_seed_transport (n N : Nat) (hNn : N ≤ n)
    (H : Finset (Reaction n)) (w : LigationWord)
    (hw : FiniteReversibleGenerated N 2 (sourceSeedField n H) w) :
    SourceLigationGenerated n (sourceSeedRestriction n N H) w := by
  have hg := finiteReversibleGenerated_mono_cap hNn (finiteReversibleGenerated_capped hw)
  obtain ⟨x,hx,he⟩ := finiteReversible_to_literalClosure hg
  rw [restrictedSplitReactions_capped_sourceSeedField] at hx
  obtain ⟨k,hk⟩ := (mem_temporaryReactionClosure _ _).mp hx
  have hw0 : 1 ≤ w.length := by rw [← he,moleculeWord_length]; unfold molLength; omega
  have hwn : w.length ≤ n := by rw [← he]; exact moleculeWord_cap x
  refine ⟨hw0,hwn,k,?_⟩
  have heq : ligationWordMolecule n w hw0 hwn = x := by
    apply sourceMolecule_eq_of_length_code
    · rw [ligationWordMolecule_length,← he,moleculeWord_length]
    · rw [ligationWordMolecule_code,ligationWordCode_eq_binaryWordCode,← he,binaryWordCode_moleculeWord]
  simpa only [heq] using hk

end
end PowerLawSmallRAF
