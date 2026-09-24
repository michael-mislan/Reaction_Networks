import proofs.PowerLawSmallRAF.FiniteSeedSourceProbability
import proofs.PowerLawSmallRAF.FiniteSeedBudgetScale

namespace PowerLawSmallRAF
open Classical MeasureTheory HordijkSteelThreshold RAF.Polymer unitInterval Filter Topology
noncomputable section

/-- Source-faithful subexponential RAF probability captures every fixed
mass below iid survival at any admissible openness floor. This is the
lower comparison; the matching upper source-survival theorem is separate. -/
theorem source_subexponential_RAF_survival_lower (a : I) (ha : 1/2 < (a : ℝ))
    (t : ℝ) (ht : t < sourceFullIntensity) (hat : (a : ℝ) ≤ 1-Real.exp (-t))
    (c : ENNReal) (hc : c < staticSurvival a) (r : ℝ) (hr : r < c.toReal) :
    ∃ N : Nat,
      (∀ b : ℝ, 0<b → ∀ᶠ n : Nat in atTop,
        (sourceFiniteSeedConstructionBudget N n : ℝ) < (2 : ℝ)^(b*(n : ℝ))) ∧
      (∀ᶠ n : Nat in atTop, r < sourceBoundedRevRAFProbability (2-2/(n : ℝ)) n
        (sourceFiniteSeedConstructionBudget N n)) := by
  let δ := (c.toReal-r)/4
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hmid : r+2*δ < c.toReal-δ := by dsimp [δ]; linarith
  obtain ⟨m,N,_,_,hseed⟩ := source_vanishing_low_rows_seed_eventually a ha t ht hat δ hδ c hc (r+2*δ) hmid
  have he := (sourceFiniteSeedTotalError_tendsto_zero N m).eventually (gt_mem_nhds hδ)
  refine ⟨N,fun _ hb => sourceFiniteSeedBudget_subexponential N hb,?_⟩
  filter_upwards [hseed,he,sourceFiniteSeedMass_eventually_le_source N m,targetUnion_eventual_conditions]
    with n hs herr hsource hcond
  have hLn : targetNucleusLength n ≤ n := hcond.2.2.2.1.trans (Nat.div_le_self _ _)
  have hh := hs (targetNucleusLength n) hLn
  linarith

end
end PowerLawSmallRAF
