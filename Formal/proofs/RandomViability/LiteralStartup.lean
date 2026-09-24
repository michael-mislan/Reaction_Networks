import proofs.RandomViability.Startup

namespace RandomViability
open Classical Filter Topology RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section

/-- Counts are multisets, so repeated reactants, including catalyst/substrate
coincidences, require their full molecular multiplicity. -/
inductive LiteralStep {n : ℕ} (c : SourceMoleculeFibreConfig n) :
    Multiset (Molecule n) → Multiset (Molecule n) → Prop
  | feed (A : Multiset (Molecule n)) (f : Molecule n) (hf : f ∈ binaryFood n 2) :
      LiteralStep c A (A + {f})
  | dilute (A : Multiset (Molecule n)) (x : Molecule n) :
      LiteralStep c (A + {x}) A
  | forward (A : Multiset (Molecule n)) (r : Reaction n) (x : Molecule n)
      (hc : r ∈ c x) :
      LiteralStep c (A + {reactionLeft r, reactionRight r, x})
        (A + {reactionProduct r, x})
  | reverse (A : Multiset (Molecule n)) (r : Reaction n) (x : Molecule n)
      (hc : r ∈ c x) :
      LiteralStep c (A + {reactionProduct r, x})
        (A + {reactionLeft r, reactionRight r, x})

inductive LiteralReach {n : ℕ} (c : SourceMoleculeFibreConfig n) :
    Multiset (Molecule n) → Multiset (Molecule n) → Prop
  | refl (A) : LiteralReach c A A
  | tail {A B C} : LiteralReach c A B → LiteralStep c B C → LiteralReach c A C

def FoodSupported {n : ℕ} (A : Multiset (Molecule n)) : Prop :=
  ∀ x ∈ A, x ∈ binaryFood n 2

theorem literal_step_food_invariant {n : ℕ} {c : SourceMoleculeFibreConfig n}
    (hc : ¬ FoodIgnition c) {A B : Multiset (Molecule n)}
    (h : LiteralStep c A B) (hA : FoodSupported A) : FoodSupported B := by
  cases h with
  | feed A f hf =>
    intro x hx
    have hh : x ∈ A ∨ x = f := by simpa using hx
    rcases hh with hx | rfl
    · exact hA x hx
    · exact hf
  | dilute A x =>
    intro y hy
    exact hA y (by simp [hy])
  | forward A r x hcat =>
    exfalso
    apply hc
    refine ⟨x, hA x (by simp), r, Or.inl ?_, hcat⟩
    intro y hy
    have hh : y = reactionLeft r ∨ y = reactionRight r := by
      simpa [binaryPolymerCRS] using hy
    rcases hh with rfl | rfl <;> apply hA <;> simp
  | reverse A r x hcat =>
    exfalso
    apply hc
    refine ⟨x, hA x (by simp), r, Or.inr ?_, hcat⟩
    intro y hy
    have hh : y = reactionProduct r := by simpa [binaryPolymerCRS] using hy
    subst y
    exact hA _ (by simp)

theorem literal_reach_food_invariant {n : ℕ} {c : SourceMoleculeFibreConfig n}
    (hc : ¬ FoodIgnition c) {A B : Multiset (Molecule n)}
    (h : LiteralReach c A B) (hA : FoodSupported A) : FoodSupported B := by
  induction h with
  | refl => exact hA
  | tail _ hstep ih => exact literal_step_food_invariant hc hstep ih

def FoodEscape {n : ℕ} (c : SourceMoleculeFibreConfig n) : Prop :=
  ∃ A B : Multiset (Molecule n), FoodSupported A ∧ LiteralReach c A B ∧ ¬ FoodSupported B

theorem foodEscape_implies_ignition {n : ℕ} {c : SourceMoleculeFibreConfig n}
    (h : FoodEscape c) : FoodIgnition c := by
  by_contra hc
  obtain ⟨A,B,hA,hreach,hB⟩ := h
  exact hB (literal_reach_food_invariant hc hreach hA)

/-- Probability over the exact capped-Zipf source of ANY feasible escape history,
allowing arbitrary food counts, feed histories and positive time/volume choices.
This is stronger than a fixed-initialization finite-horizon reachability bound. -/
theorem literal_foodEscape_mass_tendsto_zero :
    Tendsto (fun n : ℕ => eventMass (2-2/(n : ℝ)) n FoodEscape) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds foodIgnition_mass_tendsto_zero
  · filter_upwards [sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n ha
    exact eventMass_nonneg _ n ha _
  · filter_upwards [sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n ha
    exact eventMass_mono _ n ha (fun _ h => foodEscape_implies_ignition h)

end
end RandomViability
