import Mathlib.Data.Fintype.Pigeonhole
import proofs.CoreInteraction.MAF.Residual

/-!
The fixed-threshold compensation argument.  A cycle certificate is represented
by a total signed transition on the finite type of active factors together with
two distinct iterate times at which the active factor repeats.  The `via`
coordinate records the actual shared species carrying each deficit.
-/

namespace CoreInteraction

variable {Species Reaction Factor CoreId : Type}
variable [Fintype Species] [Fintype Reaction] [Fintype Factor]
variable [DecidableEq Species] [DecidableEq Factor]
variable {Q : SourceNetwork Species Reaction}

namespace Factorization

def ActiveFactor (fac : Factorization Q Factor CoreId) (x : Reaction → ℝ) :=
  {f : Factor // fac.FactorActive x f}

structure SignedStep (fac : Factorization Q Factor CoreId) (q : ℝ)
    (x : Reaction → ℝ) (f : fac.ActiveFactor x) where
  species : Species
  target : fac.ActiveFactor x
  target_ne : target.1 ≠ f.1
  source_incident : fac.support f.1 species
  target_incident : fac.support target.1 species
  source_negative : fac.residual q x f.1 species < 0
  target_positive : 0 < fac.residual q x target.1 species

def SignedInteractionCycle (fac : Factorization Q Factor CoreId) (q : ℝ)
    (x : Reaction → ℝ) : Prop :=
  ∃ (next : fac.ActiveFactor x → fac.ActiveFactor x)
      (via : fac.ActiveFactor x → Species)
      (start : fac.ActiveFactor x) (m n : ℕ),
    m < n ∧ (next^[m]) start = (next^[n]) start ∧
    ∀ f,
      (next f).1 ≠ f.1 ∧
      fac.support f.1 (via f) ∧ fac.support (next f).1 (via f) ∧
      fac.residual q x f.1 (via f) < 0 ∧
      0 < fac.residual q x (next f).1 (via f)

omit [Fintype Species] [Fintype Factor] [DecidableEq Species] in
theorem positive_residual_active (fac : Factorization Q Factor CoreId)
    (q : ℝ) (x : Reaction → ℝ) (hx : FluxNonnegative x)
    {f : Factor} {s : Species} (hpos : 0 < fac.residual q x f s) :
    fac.FactorActive x f := by
  by_contra hnot
  have hzero : fac.residual q x f s = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    by_cases hown : fac.owner r = f
    · have hxr : x r = 0 := by
        apply le_antisymm
        · apply le_of_not_gt
          intro hxpos
          exact hnot ⟨r, hown, hxpos⟩
        · exact hx r
      simp [hown, hxr]
    · simp [hown]
  linarith

omit [Fintype Species] [Fintype Factor] [DecidableEq Species] [DecidableEq Factor] in
theorem exists_active_factor (fac : Factorization Q Factor CoreId)
    (q : ℝ) (x : Reaction → ℝ) (hglobal : fac.GloballyFeasible q x) :
    Nonempty (fac.ActiveFactor x) := by
  have hxne := hglobal.2.1
  have hex : ∃ r, x r ≠ 0 := by
    by_contra hnot
    apply hxne
    funext r
    by_contra hr
    exact hnot ⟨r, hr⟩
  obtain ⟨r, hr⟩ := hex
  have hrpos : 0 < x r := lt_of_le_of_ne (hglobal.1 r) (Ne.symm hr)
  exact ⟨⟨fac.owner r, fac.active_of_positive_owned hrpos⟩⟩

omit [Fintype Species] [DecidableEq Species] in
theorem signed_step_exists (fac : Factorization Q Factor CoreId)
    (q : ℝ) (x : Reaction → ℝ) (hglobal : fac.GloballyFeasible q x)
    (hnolocal : ∀ f, fac.FactorActive x f → ¬ fac.LocallyFeasible q x f)
    (f : fac.ActiveFactor x) : Nonempty (fac.SignedStep q x f) := by
  have hprivate : ∀ s, fac.IsPrivate f.1 s → 0 ≤ fac.residual q x f.1 s := by
    intro s hs
    exact fac.globallyFeasible_private_nonneg q x hglobal hs
  have hnegative := fac.local_or_negative_interface q x f.2 hprivate
  rcases hnegative with hlocal | ⟨s, _hsinterface, hfs, hneg⟩
  · exact False.elim (hnolocal f.1 f.2 hlocal)
  · obtain ⟨g, hgf, hgs, hpos⟩ :=
      fac.negative_has_positive_compensator q x (hglobal.2.2 s) hneg
        (fun g hg => by
          by_contra hnot
          rw [fac.residual_eq_zero_of_not_support q x hnot] at hg
          linarith)
    have hgactive : fac.FactorActive x g :=
      fac.positive_residual_active q x hglobal.1 hpos
    exact ⟨{
      species := s
      target := ⟨g, hgactive⟩
      target_ne := hgf
      source_incident := hfs
      target_incident := hgs
      source_negative := hneg
      target_positive := hpos
    }⟩

omit [Fintype Species] [DecidableEq Species] in
/-- `MAF-SYNERGY-CYCLE`: global feasibility with no active locally feasible
factor produces a total signed transition and hence a repeated active incidence
state.  No optimizer or division is used. -/
theorem maf_globalFeasible_implies_signedCycle
    (fac : Factorization Q Factor CoreId) (q : ℝ) (x : Reaction → ℝ)
    (hglobal : fac.GloballyFeasible q x)
    (hnolocal : ∀ f, fac.FactorActive x f → ¬ fac.LocallyFeasible q x f) :
    fac.SignedInteractionCycle q x := by
  classical
  let step : ∀ f : fac.ActiveFactor x, fac.SignedStep q x f :=
    fun f => Classical.choice (fac.signed_step_exists q x hglobal hnolocal f)
  let next : fac.ActiveFactor x → fac.ActiveFactor x := fun f => (step f).target
  let via : fac.ActiveFactor x → Species := fun f => (step f).species
  let start : fac.ActiveFactor x := Classical.choice (fac.exists_active_factor q x hglobal)
  letI : Finite (fac.ActiveFactor x) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  obtain ⟨m, n, hmn, hrepeat⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (next^[k]) start)
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · refine ⟨next, via, start, m, n, hlt, hrepeat, ?_⟩
    intro f
    exact ⟨(step f).target_ne, (step f).source_incident,
      (step f).target_incident, (step f).source_negative, (step f).target_positive⟩
  · refine ⟨next, via, start, n, m, hgt, hrepeat.symm, ?_⟩
    intro f
    exact ⟨(step f).target_ne, (step f).source_incident,
      (step f).target_incident, (step f).source_negative, (step f).target_positive⟩

end Factorization

end CoreInteraction
