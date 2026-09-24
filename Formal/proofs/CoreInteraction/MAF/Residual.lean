import proofs.CoreInteraction.Incidence

/-! Boundary residual semantics at a fixed MAF threshold. -/

namespace CoreInteraction

variable {Species Reaction Factor CoreId : Type}
variable [Fintype Species] [Fintype Reaction] [Fintype Factor]
variable [DecidableEq Species] [DecidableEq Factor]
variable {Q : SourceNetwork Species Reaction}

namespace Factorization

def FluxNonnegative (x : Reaction → ℝ) : Prop := ∀ r, 0 ≤ x r

def FactorActive (fac : Factorization Q Factor CoreId)
    (x : Reaction → ℝ) (f : Factor) : Prop :=
  ∃ r, fac.owner r = f ∧ 0 < x r

def LocallyFeasible (fac : Factorization Q Factor CoreId) (q : ℝ)
    (x : Reaction → ℝ) (f : Factor) : Prop :=
  fac.FactorActive x f ∧ ∀ s, 0 ≤ fac.residual q x f s

def GloballyFeasible (_fac : Factorization Q Factor CoreId) (q : ℝ)
    (x : Reaction → ℝ) : Prop :=
  FluxNonnegative x ∧ x ≠ 0 ∧ ∀ s, 0 ≤ globalResidual Q q x s

omit [Fintype Species] [Fintype Reaction] [Fintype Factor]
    [DecidableEq Species] [DecidableEq Factor] in
theorem active_of_positive_owned (fac : Factorization Q Factor CoreId)
    {x : Reaction → ℝ} {r : Reaction} (hr : 0 < x r) :
    fac.FactorActive x (fac.owner r) :=
  ⟨r, rfl, hr⟩

omit [Fintype Species] [DecidableEq Species] in
/-- `PRIVATE-NONNEG`: no neighboring factor can compensate on a private
species, so its local residual equals the global residual. -/
theorem private_residual_eq_global (fac : Factorization Q Factor CoreId)
    (q : ℝ) (x : Reaction → ℝ) {f : Factor} {s : Species}
    (hprivate : fac.IsPrivate f s) :
    fac.residual q x f s = globalResidual Q q x s := by
  rw [← fac.residual_sum_eq_global q x s]
  rw [Finset.sum_eq_single f]
  · intro g _ hgf
    exact fac.residual_eq_zero_of_not_support q x (fun hgs => hgf (hprivate.2 g hgs))
  · simp

omit [Fintype Species] [DecidableEq Species] in
theorem globallyFeasible_private_nonneg (fac : Factorization Q Factor CoreId)
    (q : ℝ) (x : Reaction → ℝ) (hglobal : fac.GloballyFeasible q x)
    {f : Factor} {s : Species} (hprivate : fac.IsPrivate f s) :
    0 ≤ fac.residual q x f s := by
  rw [fac.private_residual_eq_global q x hprivate]
  exact hglobal.2.2 s

omit [Fintype Species] [DecidableEq Species] in
/-- `LOCAL-OR-NEG-BOUNDARY`: once private coordinates are nonnegative, an
active factor that is not locally feasible has a negative interface residual. -/
theorem local_or_negative_interface (fac : Factorization Q Factor CoreId)
    (q : ℝ) (x : Reaction → ℝ) {f : Factor} (hactive : fac.FactorActive x f)
    (hprivate : ∀ s, fac.IsPrivate f s → 0 ≤ fac.residual q x f s) :
    fac.LocallyFeasible q x f ∨
      ∃ s, fac.IsInterface s ∧ fac.support f s ∧ fac.residual q x f s < 0 := by
  by_cases hlocal : ∀ s, 0 ≤ fac.residual q x f s
  · exact Or.inl ⟨hactive, hlocal⟩
  · right
    rw [not_forall] at hlocal
    obtain ⟨s, hsnot⟩ := hlocal
    have hsneg : fac.residual q x f s < 0 := lt_of_not_ge hsnot
    have hfs : fac.support f s := by
      by_contra hnot
      rw [fac.residual_eq_zero_of_not_support q x hnot] at hsneg
      linarith
    rcases fac.support_private_or_interface hfs with hp | hi
    · exact False.elim (not_lt_of_ge (hprivate s hp) hsneg)
    · exact ⟨s, hi, hfs, hsneg⟩

omit [Fintype Species] [DecidableEq Species] in
/-- `NEG-HAS-POS-COMPENSATOR`: a negative incident contribution inside a
nonnegative global sum has a distinct positive incident compensator. -/
theorem negative_has_positive_compensator (fac : Factorization Q Factor CoreId)
    (q : ℝ) (x : Reaction → ℝ) {f : Factor} {s : Species}
    (hglobal : 0 ≤ globalResidual Q q x s)
    (hneg : fac.residual q x f s < 0)
    (hsupport_pos : ∀ g, 0 < fac.residual q x g s → fac.support g s) :
    ∃ g, g ≠ f ∧ fac.support g s ∧ 0 < fac.residual q x g s := by
  have hsum : 0 ≤ ∑ g : Factor, fac.residual q x g s := by
    simpa [fac.residual_sum_eq_global q x s] using hglobal
  by_contra hnone
  have hnonpos : ∀ g, g ≠ f → fac.residual q x g s ≤ 0 := by
    intro g hgf
    by_contra hnot
    have hpos : 0 < fac.residual q x g s := lt_of_not_ge hnot
    exact hnone ⟨g, hgf, hsupport_pos g hpos, hpos⟩
  have hrest : (∑ g ∈ (Finset.univ.erase f), fac.residual q x g s) ≤ 0 := by
    exact Finset.sum_nonpos fun g hg => hnonpos g (Finset.ne_of_mem_erase hg)
  have hsplit :
      (∑ g : Factor, fac.residual q x g s) =
        (∑ g ∈ (Finset.univ.erase f), fac.residual q x g s) +
          fac.residual q x f s := by
    exact (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ f)).symm
  rw [hsplit] at hsum
  linarith

end Factorization

end CoreInteraction
