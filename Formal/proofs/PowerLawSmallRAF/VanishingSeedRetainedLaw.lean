import proofs.PowerLawSmallRAF.VanishingSeedMassAverage

namespace PowerLawSmallRAF
open Classical MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete unitInterval
open Filter Topology
noncomputable section

def sourceVanishingLowRowsSeedMass (n N m L : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    ∑ A : SourceLowOwnerGroup n d → Finset (Reaction n),
      bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A *
        (if sourceFiniteSeedEvent n N m (bernoulliRowsUnion A) ∧
          SourceAboveSeedMarked n m L (bernoulliRowsUnion A) then 1 else 0)

theorem sourceVanishingLowRowsSeedMass_eq (n N m L : Nat) :
    sourceVanishingLowRowsSeedMass n N m L = sourceVanishingSeedExtensionMass n N m L := by
  unfold sourceVanishingLowRowsSeedMass sourceVanishingSeedExtensionMass
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  rw [bernoulliRows_union_expectation (sourceVanishingLowOwnerParameter n d)
    (fun H => if sourceFiniteSeedEvent n N m H ∧ SourceAboveSeedMarked n m L H then 1 else 0)]
  unfold sourceSeedExtensionMass sourceVanishingLowUnionParameter
  apply Finset.sum_congr rfl
  intro H _
  split_ifs <;> simp

/-- The retained low rows, including their real owner identities, capture
arbitrarily prescribed mass below survival minus the chosen seed-extension
error. No global iid law is asserted for the original source. -/
theorem source_vanishing_low_rows_seed_eventually (a : I) (ha : 1/2 < (a : ℝ))
    (t : ℝ) (ht : t < sourceFullIntensity) (hat : (a : ℝ) ≤ 1-Real.exp (-t))
    (ε : ℝ) (hε : 0 < ε) (c : ENNReal) (hc : c < staticSurvival a)
    (r : ℝ) (hr : r < c.toReal-ε) :
    ∃ m N : Nat, 2 ≤ m ∧ m ≤ N ∧
      ∀ᶠ n : Nat in atTop, ∀ L : Nat, L ≤ n → r < sourceVanishingLowRowsSeedMass n N m L := by
  obtain ⟨m,N,hm,hNm,hbound⟩ := source_vanishing_seed_survival_average a ha t hat ε hε c hc
  have htend := ((tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).sub
    (sourceVanishingLowUnionFailureMass_tendsto_zero t ht)).const_mul
    (c.toReal-ε)
  have htend' : Tendsto (fun n => (c.toReal-ε)*(1-sourceVanishingLowUnionFailureMass t n))
      atTop (𝓝 (c.toReal-ε)) := by simpa using htend
  have he := htend'.eventually (lt_mem_nhds hr)
  refine ⟨m,N,hm,hNm,?_⟩
  filter_upwards [he,eventually_ge_atTop 4,eventually_ge_atTop N] with n hn h4 hN
  intro L hLn
  rw [sourceVanishingLowRowsSeedMass_eq]
  exact hn.trans_le (hbound n L h4 hN hLn)

end
end PowerLawSmallRAF
