import proofs.PowerLawSmallRAF.FixedSeedSurvivalApproximation
import proofs.PowerLawSmallRAF.FixedSeedMarkProbability

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete Filter Topology MeasureTheory unitInterval HordijkSteelThreshold
open scoped ENNReal
noncomputable section

/-- A single fixed seed captures any mass strictly below iid survival,
while its extension to every larger finite nucleus has arbitrarily small
unconditional marking failure. This is an iid interface, not a power-law
conditional-minimum conclusion. -/
theorem fixed_seed_uniform_extension_bridge (a : I) (ha : 1/2 < (a : ℝ))
    (ε : ℝ) (hε : 0<ε) (c : ENNReal) (hc : c < staticSurvival a) :
    ∃ m N : Nat, 2 ≤ m ∧ m ≤ N ∧
      (c < staticReactionMeasure N a {ω | ∀ w ∈ actualBinaryWords m,
        ∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions ω), moleculeWord x = w}) ∧
      (∀ n L : Nat, L ≤ n → sourceAboveSeedFailureMass (a : ℝ) n m L < ε) := by
  obtain ⟨m,N,hm,hNm,htail,hseed⟩ :=
    fixed_seed_captures_survival_with_small_extension_error a ha ε hε c hc
  refine ⟨m,N,hm,hNm,hseed,?_⟩
  intro n L hLn
  exact (sourceAboveSeedFailureMass_bound (a : ℝ) ha a.property.2 n m L hLn).trans_lt htail

/-- The actual selected extra channels and owners obey the old power
budget; only the already generated fixed base must be counted in addition. -/
theorem source_seeded_nucleus_selection_power_budget {Owner : Type*} [DecidableEq Owner]
    (n m L : Nat) (hLn : L ≤ n) (B : Finset (Reaction n))
    (hseed : ∀ w : LigationWord, 1 ≤ w.length → w.length ≤ m → SourceLigationGenerated n B w)
    (A : Owner → Finset (Reaction n))
    (hmark : ∀ w ∈ sourceAboveSeedWords m L, ∃ (hn : w.length ≤ n) (i : ligationCuts w)
      (x : Owner), ligationCutReaction n w hn i ∈ A x) :
    ∃ (S : Finset (Reaction n)) (C : Finset Owner),
      S.card ≤ 2^(L+1) ∧ C.card ≤ 2^(L+1) ∧ (B ∪ S).card ≤ B.card+2^(L+1) ∧
      (∀ r ∈ S, ∃ x ∈ C, r ∈ A x) ∧
      (∀ x ∈ C, ∃ r ∈ S, r ∈ A x) ∧
      (∀ w : LigationWord, 1 ≤ w.length → w.length ≤ L → SourceLigationGenerated n (B ∪ S) w) := by
  obtain ⟨S,C,hS,hC,hBS,hcovered,hused,hgen⟩ := source_seeded_nucleus_bounded_selection n m L
    hLn B hseed A (sourceAboveSeedWords m L) (mem_sourceAboveSeedWords m L) hmark
  have hb := sourceAboveSeedWords_card_le m L
  exact ⟨S,C,hS.trans hb,hC.trans hb,hBS.trans (Nat.add_le_add_left hb _),hcovered,hused,hgen⟩

end
end PowerLawSmallRAF
