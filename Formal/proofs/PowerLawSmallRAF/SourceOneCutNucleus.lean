import proofs.PowerLawSmallRAF.LigationSourceClosure

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
noncomputable section

theorem sourceLigationGenerated_food (n : Nat) (T : Finset (Reaction n))
    (w : LigationWord) (h0 : 1 ≤ w.length) (h2 : w.length ≤ 2)
    (hn : w.length ≤ n) : SourceLigationGenerated n T w := by
  refine ⟨h0, hn, 0, ?_⟩
  simpa [revClosureAt, binaryPolymerCRS, binaryFood, ligationWordMolecule_length] using h2

/-- A marked split for every nonfood word suffices to generate the entire
nucleus from the original food. No catalyst-generation assumption is hidden here. -/
theorem source_one_cut_nucleus_generated (n L : Nat) (hLn : L ≤ n)
    (T : Finset (Reaction n))
    (hcut : ∀ (w : LigationWord) (_h3 : 3 ≤ w.length) (hL : w.length ≤ L),
      ∃ i : ligationCuts w, ligationCutReaction n w (hL.trans hLn) i ∈ T) :
    ∀ (w : LigationWord), 1 ≤ w.length → w.length ≤ L →
      SourceLigationGenerated n T w := by
  intro w
  induction hw : w.length using Nat.strong_induction_on generalizing w with
  | h k ih =>
    intro h0 hL
    have h0w : 1 ≤ w.length := by omega
    have hLw : w.length ≤ L := by omega
    by_cases h2 : w.length ≤ 2
    · exact sourceLigationGenerated_food n T w h0w h2 (hLw.trans hLn)
    · obtain ⟨i, hi⟩ := hcut w (by omega) hLw
      have hic := Finset.mem_Ioo.mp i.property
      apply sourceLigationGenerated_of_cut n T w (hLw.trans hLn) i hi
      · have hlen : (w.take i.val).length = i.val := List.length_take_of_le (by omega)
        apply ih i.val (by omega) (w.take i.val) hlen
        · omega
        · omega
      · have hlen : (w.drop i.val).length = w.length-i.val := List.length_drop
        apply ih (w.length-i.val) (by omega) (w.drop i.val) hlen
        · omega
        · omega

end
end PowerLawSmallRAF
