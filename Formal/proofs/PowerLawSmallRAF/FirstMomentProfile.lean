import proofs.PowerLawSmallRAF.FactorialMoments

namespace PowerLawSmallRAF

variable {R : Type*} [DecidableEq R]

def eligibleSupports (ambient : Finset R) (eligible : Finset R → Prop)
    [DecidablePred eligible] (r : Nat) : Finset (Finset R) :=
  ambient.powerset.filter fun S => eligible S ∧ S.card = r

def supportProfileCount (ambient : Finset R) (eligible : Finset R → Prop)
    [DecidablePred eligible] (closureSize : Finset R → Nat)
    (r q : Nat) : Nat :=
  ((eligibleSupports ambient eligible r).filter fun S =>
    closureSize S = q).card

noncomputable def expectedEligibleCount
    (ambient : Finset R) (eligible : Finset R → Prop)
    [DecidablePred eligible] (r : Nat) (weight : Finset R → ℝ) : ℝ :=
  ∑ S ∈ eligibleSupports ambient eligible r, weight S

omit [DecidableEq R] in
/-- Exact first-moment fiber decomposition.  The hypotheses say that closure
sizes lie in `0, ..., Q` and that witness weight depends on a support only
through that closure size. -/
theorem expectedEligibleCount_eq_profileSum
    (ambient : Finset R) (eligible : Finset R → Prop)
    [DecidablePred eligible] (closureSize : Finset R → Nat)
    (r Q : Nat) (weight : Finset R → ℝ) (psi : Nat → ℝ)
    (hclosure : ∀ S ∈ eligibleSupports ambient eligible r,
      closureSize S ≤ Q)
    (hweight : ∀ S ∈ eligibleSupports ambient eligible r,
      weight S = psi (closureSize S)) :
    expectedEligibleCount ambient eligible r weight =
      ∑ q ∈ Finset.range (Q + 1),
        (supportProfileCount ambient eligible closureSize r q : ℝ) * psi q := by
  rw [expectedEligibleCount]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := eligibleSupports ambient eligible r)
    (t := Finset.range (Q + 1)) (g := closureSize)
    (fun S hS => Finset.mem_range.2 (Nat.lt_succ_of_le (hclosure S hS))) weight]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [supportProfileCount]
  calc
    (∑ S ∈ eligibleSupports ambient eligible r with closureSize S = q,
        weight S) =
        ∑ S ∈ eligibleSupports ambient eligible r with closureSize S = q,
          psi q := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [hweight S (Finset.mem_filter.mp hS).1,
        (Finset.mem_filter.mp hS).2]
    _ = (((eligibleSupports ambient eligible r).filter fun S =>
        closureSize S = q).card : ℝ) * psi q := by
      simp only [Finset.sum_const, nsmul_eq_mul]

omit [DecidableEq R] in
/-- The campaign formula `E N_{n,r} = sum_q A_{n,r,q} Psi_n(r,q)` in its
power-law coverage specialization. -/
theorem expectedRAFCount_eq_powerLawProfileSum
    (ambient : Finset R) (foodGenerated : Finset R → Prop)
    [DecidablePred foodGenerated] (closureSize : Finset R → Nat)
    (r Q : Nat) (weight : Finset R → ℝ) (u : Nat → ℝ)
    (hclosure : ∀ S ∈ eligibleSupports ambient foodGenerated r,
      closureSize S ≤ Q)
    (hweight : ∀ S ∈ eligibleSupports ambient foodGenerated r,
      weight S = coverageInclusionExclusion u r (closureSize S)) :
    expectedEligibleCount ambient foodGenerated r weight =
      ∑ q ∈ Finset.range (Q + 1),
        (supportProfileCount ambient foodGenerated closureSize r q : ℝ) *
          coverageInclusionExclusion u r q := by
  exact expectedEligibleCount_eq_profileSum ambient foodGenerated closureSize
    r Q weight (fun q => coverageInclusionExclusion u r q) hclosure hweight

end PowerLawSmallRAF
