import Mathlib.Combinatorics.SimpleGraph.Acyclic
import proofs.CoreInteraction.MAF.CycleWitness

/-!
The signed compensation transition produces a reduced closed walk in the
factor--species incidence graph.  An incidence forest has no such walk.
-/

namespace CoreInteraction

variable {Species Reaction Factor CoreId : Type}
variable [Fintype Species] [Fintype Reaction] [Fintype Factor]
variable [DecidableEq Species] [DecidableEq Factor]
variable {Q : SourceNetwork Species Reaction}

namespace Factorization

def compensationWalk (fac : Factorization Q Factor CoreId)
    {A : Type} (next : A → A) (via : A → Species) (val : A → Factor)
    (hsource : ∀ a, fac.support (val a) (via a))
    (htarget : ∀ a, fac.support (val (next a)) (via a)) :
    (n : ℕ) → (a : A) →
      fac.incidenceGraph.Walk (Sum.inl (val a))
        (Sum.inl (val ((next^[n]) a)))
  | 0, a => .nil
  | n + 1, a => by
      rw [Function.iterate_succ_apply]
      exact .cons (fac.incidenceGraph_adj_factor_species _ _ |>.2 (hsource a))
        (.cons (fac.incidenceGraph_adj_species_factor _ _ |>.2 (htarget a))
          (compensationWalk fac next via val hsource htarget n (next a)))

omit [Fintype Species] [Fintype Reaction] [Fintype Factor]
    [DecidableEq Species] [DecidableEq Factor] in
@[simp] theorem compensationWalk_length (fac : Factorization Q Factor CoreId)
    {A : Type} (next : A → A) (via : A → Species) (val : A → Factor)
    (hsource : ∀ a, fac.support (val a) (via a))
    (htarget : ∀ a, fac.support (val (next a)) (via a))
    (n : ℕ) (a : A) :
    (fac.compensationWalk next via val hsource htarget n a).length = 2 * n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [compensationWalk, ih, Nat.mul_succ]

omit [Fintype Species] [Fintype Reaction] [Fintype Factor]
    [DecidableEq Species] [DecidableEq Factor] in
theorem compensationWalk_isChain (fac : Factorization Q Factor CoreId)
    {A : Type} (next : A → A) (via : A → Species) (val : A → Factor)
    (hsource : ∀ a, fac.support (val a) (via a))
    (htarget : ∀ a, fac.support (val (next a)) (via a))
    (hfactor : ∀ a, val (next a) ≠ val a)
    (hspecies : ∀ a, via (next a) ≠ via a)
    (n : ℕ) (a : A) :
    List.IsChain (· ≠ ·)
      (fac.compensationWalk next via val hsource htarget n a).edges := by
  induction n generalizing a with
  | zero => simp [compensationWalk]
  | succ n ih =>
      simp only [compensationWalk]
      apply List.IsChain.cons_cons
      · simpa [Sym2.eq, Sym2.rel_iff] using (hfactor a).symm
      · cases n with
        | zero => exact .singleton _
        | succ k =>
            simp only [compensationWalk]
            apply List.IsChain.cons_cons
            · simpa [Sym2.eq, Sym2.rel_iff] using (hspecies a).symm
            · exact ih (next a)

omit [Fintype Species] [Fintype Factor] [DecidableEq Species] in
theorem signedInteractionCycle_not_incidenceForest
    (fac : Factorization Q Factor CoreId) (q : ℝ) (x : Reaction → ℝ)
    (hcycle : fac.SignedInteractionCycle q x) :
    ¬ fac.IncidenceForest := by
  classical
  rcases hcycle with ⟨next, via, start, m, n, hmn, hrepeat, hstep⟩
  let val : fac.ActiveFactor x → Factor := fun f => f.1
  have hsource : ∀ f, fac.support (val f) (via f) := fun f => (hstep f).2.1
  have htarget : ∀ f, fac.support (val (next f)) (via f) := fun f => (hstep f).2.2.1
  have hfactor : ∀ f, val (next f) ≠ val f := fun f => (hstep f).1
  have hspecies : ∀ f, via (next f) ≠ via f := by
    intro f heq
    have hpos := (hstep f).2.2.2.2
    have hneg := (hstep (next f)).2.2.2.1
    rw [heq] at hneg
    linarith
  let d := n - m
  let a := (next^[m]) start
  have hd : 0 < d := Nat.sub_pos_of_lt hmn
  have hperiod : (next^[d]) a = a := by
    dsimp [d, a]
    rw [← Function.iterate_add_apply]
    rw [Nat.sub_add_cancel hmn.le]
    exact hrepeat.symm
  let w0 := fac.compensationWalk next via val hsource htarget d a
  let w : fac.incidenceGraph.Walk (Sum.inl (val a)) (Sum.inl (val a)) :=
    w0.copy rfl (congrArg (fun f => Sum.inl (val f)) hperiod)
  intro hforest
  have hwchain : List.IsChain (· ≠ ·) w.edges := by
    subst w
    simpa only [SimpleGraph.Walk.edges_copy] using
      fac.compensationWalk_isChain next via val hsource htarget
      hfactor hspecies d a
  have hwpath : w.IsPath :=
    (hforest.isPath_iff_isChain w).2 hwchain
  have hwnil : w = .nil := (w.isPath_iff_eq_nil).1 hwpath
  have hwlen : w.length = 2 * d := by
    subst w
    simpa only [SimpleGraph.Walk.length_copy] using
      fac.compensationWalk_length next via val hsource htarget d a
  rw [hwnil] at hwlen
  simp at hwlen
  omega

omit [Fintype Species] [DecidableEq Species] in
/-- `CIC-MAF-CYCLE`: global feasibility without an active locally feasible
factor forces a genuine graph cycle in the factor--species incidence graph. -/
theorem maf_globalFeasible_implies_incidenceCycle
    (fac : Factorization Q Factor CoreId) (q : ℝ) (x : Reaction → ℝ)
    (hglobal : fac.GloballyFeasible q x)
    (hnolocal : ∀ f, fac.FactorActive x f → ¬ fac.LocallyFeasible q x f) :
    ¬ fac.IncidenceForest :=
  fac.signedInteractionCycle_not_incidenceForest q x
    (fac.maf_globalFeasible_implies_signedCycle q x hglobal hnolocal)

omit [Fintype Species] [DecidableEq Species] in
theorem maf_globalFeasible_implies_exists_incidenceCycle
    (fac : Factorization Q Factor CoreId) (q : ℝ) (x : Reaction → ℝ)
    (hglobal : fac.GloballyFeasible q x)
    (hnolocal : ∀ f, fac.FactorActive x f → ¬ fac.LocallyFeasible q x f) :
    ∃ v, ∃ c : fac.incidenceGraph.Walk v v, c.IsCycle := by
  classical
  have hn := fac.maf_globalFeasible_implies_incidenceCycle q x hglobal hnolocal
  change ¬ ∀ ⦃v⦄ (c : fac.incidenceGraph.Walk v v), ¬ c.IsCycle at hn
  obtain ⟨v, hv⟩ := Classical.not_forall.mp hn
  obtain ⟨c, hc⟩ := Classical.not_forall.mp hv
  exact ⟨v, c, Classical.not_not.mp hc⟩

omit [Fintype Species] [DecidableEq Species] in
/-- On an incidence forest, every globally feasible flux exposes an active
factor whose owned reactions are already locally feasible at the same `q`. -/
theorem incidenceForest_globalFeasible_has_local
    (fac : Factorization Q Factor CoreId) (q : ℝ) (x : Reaction → ℝ)
    (hforest : fac.IncidenceForest) (hglobal : fac.GloballyFeasible q x) :
    ∃ f, fac.FactorActive x f ∧ fac.LocallyFeasible q x f := by
  by_contra hnot
  have hnolocal : ∀ f, fac.FactorActive x f → ¬ fac.LocallyFeasible q x f := by
    intro f hf hl
    exact hnot ⟨f, hf, hl⟩
  exact fac.maf_globalFeasible_implies_incidenceCycle q x hglobal hnolocal hforest

def restrictFlux (fac : Factorization Q Factor CoreId) (f : Factor)
    (x : Reaction → ℝ) (r : Reaction) : ℝ :=
  if fac.owner r = f then x r else 0

def GlobalFeasibleAt (fac : Factorization Q Factor CoreId) (q : ℝ) : Prop :=
  ∃ x, fac.GloballyFeasible q x

def FactorFeasibleAt (fac : Factorization Q Factor CoreId)
    (q : ℝ) (f : Factor) : Prop :=
  ∃ x, FluxNonnegative x ∧ fac.LocallyFeasible q x f

def IsExactThreshold (P : ℝ → Prop) (qstar : ℝ) : Prop :=
  P qstar ∧ ∀ q, P q → q ≤ qstar

omit [Fintype Species] [Fintype Reaction] [Fintype Factor]
    [DecidableEq Species] in
theorem restrictFlux_nonnegative (fac : Factorization Q Factor CoreId)
    {f : Factor} {x : Reaction → ℝ} (hx : FluxNonnegative x) :
    FluxNonnegative (fac.restrictFlux f x) := by
  intro r
  by_cases hr : fac.owner r = f <;> simp [restrictFlux, hr, hx r]

omit [Fintype Species] [Fintype Reaction] [Fintype Factor]
    [DecidableEq Species] in
theorem restrictFlux_active (fac : Factorization Q Factor CoreId)
    {f : Factor} {x : Reaction → ℝ} (hactive : fac.FactorActive x f) :
    fac.FactorActive (fac.restrictFlux f x) f := by
  obtain ⟨r, hr, hpos⟩ := hactive
  exact ⟨r, hr, by simp [restrictFlux, hr, hpos]⟩

omit [Fintype Species] [Fintype Factor] [DecidableEq Species] in
@[simp] theorem residual_restrictFlux (fac : Factorization Q Factor CoreId)
    (q : ℝ) (x : Reaction → ℝ) (f : Factor) (s : Species) :
    fac.residual q (fac.restrictFlux f x) f s = fac.residual q x f s := by
  unfold residual restrictFlux
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : fac.owner r = f <;> simp [hr]

omit [Fintype Species] [Fintype Factor] [DecidableEq Species] in
theorem globalResidual_restrictFlux (fac : Factorization Q Factor CoreId)
    (q : ℝ) (x : Reaction → ℝ) (f : Factor) (s : Species) :
    globalResidual Q q (fac.restrictFlux f x) s = fac.residual q x f s := by
  unfold globalResidual residual restrictFlux
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : fac.owner r = f <;> simp [hr]

omit [Fintype Species] [Fintype Factor] [DecidableEq Species] in
theorem factorFeasibleAt_implies_globalFeasibleAt
    (fac : Factorization Q Factor CoreId) (q : ℝ) (f : Factor)
    (hlocal : fac.FactorFeasibleAt q f) : fac.GlobalFeasibleAt q := by
  obtain ⟨x, hx, hactive, hresidual⟩ := hlocal
  let y := fac.restrictFlux f x
  refine ⟨y, fac.restrictFlux_nonnegative hx, ?_, ?_⟩
  · obtain ⟨r, hr, hpos⟩ := fac.restrictFlux_active hactive
    intro hy
    have : y r = 0 := congrFun hy r
    linarith
  · intro s
    rw [fac.globalResidual_restrictFlux q x f s]
    exact hresidual s

omit [Fintype Species] [DecidableEq Species] in
/-- `CIC-MAF-FOREST`: fixed-threshold global feasibility is exactly the
disjunction of factor feasibilities whenever the incidence graph is a forest. -/
theorem incidenceForest_globalFeasibleAt_iff
    (fac : Factorization Q Factor CoreId) (q : ℝ)
    (hforest : fac.IncidenceForest) :
    fac.GlobalFeasibleAt q ↔ ∃ f, fac.FactorFeasibleAt q f := by
  constructor
  · rintro ⟨x, hglobal⟩
    obtain ⟨f, _hactive, hlocal⟩ :=
      fac.incidenceForest_globalFeasible_has_local q x hforest hglobal
    exact ⟨f, x, hglobal.1, hlocal⟩
  · rintro ⟨f, hlocal⟩
    exact fac.factorFeasibleAt_implies_globalFeasibleAt q f hlocal

omit [Fintype Species] [DecidableEq Species] in
/-- If every factor threshold is attained and `fmax` attains their maximum,
then the global threshold on an incidence forest is exactly that maximum. -/
theorem incidenceForest_exactThreshold_max
    (fac : Factorization Q Factor CoreId) (qf : Factor → ℝ) (fmax : Factor)
    (hforest : fac.IncidenceForest)
    (hloc : ∀ f, IsExactThreshold (fun q => fac.FactorFeasibleAt q f) (qf f))
    (hmax : ∀ f, qf f ≤ qf fmax) :
    IsExactThreshold fac.GlobalFeasibleAt (qf fmax) := by
  constructor
  · apply (fac.incidenceForest_globalFeasibleAt_iff (qf fmax) hforest).2
    exact ⟨fmax, (hloc fmax).1⟩
  · intro q hq
    obtain ⟨f, hf⟩ :=
      (fac.incidenceForest_globalFeasibleAt_iff q hforest).1 hq
    exact le_trans ((hloc f).2 q hf) (hmax f)

omit [Fintype Species] [Fintype Factor] [DecidableEq Species]
    [DecidableEq Factor] in
@[simp] theorem zero_flux_not_globallyFeasible
    (fac : Factorization Q Factor CoreId) (q : ℝ) :
    ¬ fac.GloballyFeasible q (0 : Reaction → ℝ) := by
  intro h
  exact h.2.1 rfl

omit [Fintype Species] [Fintype Factor] [DecidableEq Species]
    [DecidableEq Factor] in
theorem zero_input_species_globalResidual_nonnegative
    (Q : SourceNetwork Species Reaction) (q : ℝ) (x : Reaction → ℝ)
    (s : Species) (hinput : ∀ r, Q.input s r = 0)
    (houtput : ∀ r, 0 ≤ Q.output s r) (hx : FluxNonnegative x) :
    0 ≤ globalResidual Q q x s := by
  unfold globalResidual
  apply Finset.sum_nonneg
  intro r _
  rw [hinput r]
  simp only [mul_zero, sub_zero]
  exact mul_nonneg (houtput r) (hx r)

omit [Fintype Species] [DecidableEq Species] in
/-- Stable public name for the fixed-threshold forest composition law. -/
theorem maf_incidenceForest_exact
    (fac : Factorization Q Factor CoreId) (q : ℝ)
    (hforest : fac.IncidenceForest) :
    fac.GlobalFeasibleAt q ↔ ∃ f, fac.FactorFeasibleAt q f :=
  fac.incidenceForest_globalFeasibleAt_iff q hforest

end Factorization

end CoreInteraction
