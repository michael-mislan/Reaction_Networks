import proofs.DUnstableCores.ClassicalMassAction.Rate
import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Support-preserving rational mass-action lifting

A positive rational flux and a rational parameter-rich reactivity profile can
be realized exactly by ordinary mass action after adding the same supported
integer multiplicities to both sides of every reaction.  The construction is
finite denominator clearing; the additional global scale makes every new
source exponent dominate the old literal reactant exponent.
-/

namespace DUnstableCores

open scoped BigOperators

variable {Species Reaction : Type*}

/-- Rational version of an admissible parameter-rich reactivity profile. -/
structure RationalReactivityProfile
    (Q : SourceNetwork Species Reaction) where
  value : Matrix Reaction Species ℚ
  nonneg : ∀ r s, 0 ≤ value r s
  positive_of_reactant : ∀ r s, Q.Reactant s r → 0 < value r s
  zero_of_not_reactant : ∀ r s, ¬ Q.Reactant s r → value r s = 0

namespace RationalReactivityProfile

variable {Q : SourceNetwork Species Reaction}

theorem positive_iff (P : RationalReactivityProfile Q) (r : Reaction) (s : Species) :
    0 < P.value r s ↔ Q.Reactant s r := by
  constructor
  · intro h
    by_contra hn
    rw [P.zero_of_not_reactant r s hn] at h
    exact (lt_irrefl 0) h
  · exact P.positive_of_reactant r s

/-- Cast a rational profile to the real reactivity interface used by the
Jacobian library. -/
noncomputable def toReactivity (P : RationalReactivityProfile Q) : Reactivity Q where
  value := fun r s => (P.value r s : ℝ)
  nonneg := by intro r s; exact_mod_cast P.nonneg r s
  positive_of_reactant := by intro r s h; exact_mod_cast P.positive_of_reactant r s h
  zero_of_not_reactant := by intro r s h; exact_mod_cast P.zero_of_not_reactant r s h

end RationalReactivityProfile

section Construction

variable [Fintype Species] [DecidableEq Species]
variable [Fintype Reaction] [DecidableEq Reaction]
variable {Q : SourceNetwork Species Reaction}

/-- Rational kinetic-order ratios `R_ji / v_j`, transposed into the literal
source-matrix orientation. -/
def rationalLiftRatio (P : RationalReactivityProfile Q) (v : Reaction → ℚ) :
    Matrix Species Reaction ℚ := fun s r => P.value r s / v r

/-- A deliberately simple global scale which is strictly larger than every
old reactant exponent. -/
def rationalLiftScale (Q : SourceNetwork Species Reaction) : ℕ :=
  1 + ∑ s : Species, ∑ r : Reaction, Q.reactant s r

/-- Denominator-cleared nonnegative base exponent matrix. -/
def rationalLiftBaseExponent (P : RationalReactivityProfile Q) (v : Reaction → ℚ) :
    Matrix Species Reaction ℕ :=
  fun s r => ((rationalLiftRatio P v).num s r).toNat

/-- Final exponent matrix.  The extra scale guarantees domination of the old
reactant matrix, so it is literally obtainable by catalytic padding. -/
def rationalLiftExponent (P : RationalReactivityProfile Q) (v : Reaction → ℚ) :
    Matrix Species Reaction ℕ :=
  fun s r => rationalLiftScale Q * rationalLiftBaseExponent P v s r

omit [Fintype Species] [DecidableEq Species]
  [Fintype Reaction] [DecidableEq Reaction] in
theorem rationalLiftRatio_nonneg (P : RationalReactivityProfile Q)
    (v : Reaction → ℚ) (hv : ∀ r, 0 < v r) (s : Species) (r : Reaction) :
    0 ≤ rationalLiftRatio P v s r := by
  exact div_nonneg (P.nonneg r s) (hv r).le

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem rationalLiftBaseExponent_cast (P : RationalReactivityProfile Q)
    (v : Reaction → ℚ) (hv : ∀ r, 0 < v r) (s : Species) (r : Reaction) :
    (rationalLiftBaseExponent P v s r : ℚ) =
      ((rationalLiftRatio P v).den : ℚ) * rationalLiftRatio P v s r := by
  let A := rationalLiftRatio P v
  have hdenPos : 0 < A.den := Nat.pos_of_ne_zero A.den_ne_zero
  have hnumNonnegative : (0 : ℤ) ≤ A.num s r := by
    have hdiv : (A.num s r : ℚ) / (A.den : ℚ) = A s r := A.num_div_den s r
    have hdenRat : (0 : ℚ) < A.den := by exact_mod_cast hdenPos
    have hnumRat : (0 : ℚ) ≤ A.num s r := by
      have hdenNe : (A.den : ℚ) ≠ 0 := ne_of_gt hdenRat
      have heq : (A.num s r : ℚ) = A s r * (A.den : ℚ) :=
        (div_eq_iff hdenNe).mp hdiv
      rw [heq]
      exact mul_nonneg (rationalLiftRatio_nonneg P v hv s r) hdenRat.le
    exact_mod_cast hnumRat
  have htoNat : ((A.num s r).toNat : ℤ) = A.num s r :=
    Int.toNat_of_nonneg hnumNonnegative
  have hcast : (rationalLiftBaseExponent P v s r : ℚ) = (A.num s r : ℚ) := by
    exact_mod_cast htoNat
  have hdiv : (A.num s r : ℚ) / (A.den : ℚ) = A s r := A.num_div_den s r
  rw [hcast]
  have hdenNe : (A.den : ℚ) ≠ 0 := by exact_mod_cast A.den_ne_zero
  apply (div_eq_iff hdenNe).mp at hdiv
  simpa [A, mul_comm] using hdiv

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem rationalLiftBaseExponent_pos_iff (P : RationalReactivityProfile Q)
    (v : Reaction → ℚ) (hv : ∀ r, 0 < v r) (s : Species) (r : Reaction) :
    0 < rationalLiftBaseExponent P v s r ↔ Q.Reactant s r := by
  have hdenPos : (0 : ℚ) < (rationalLiftRatio P v).den := by
    exact_mod_cast Nat.pos_of_ne_zero (rationalLiftRatio P v).den_ne_zero
  have hcast := rationalLiftBaseExponent_cast P v hv s r
  constructor
  · intro h
    have hrat : 0 < rationalLiftRatio P v s r := by
      have hbaseRat : (0 : ℚ) < rationalLiftBaseExponent P v s r := by exact_mod_cast h
      nlinarith
    have hprofile : 0 < P.value r s := by
      rw [rationalLiftRatio] at hrat
      rcases div_pos_iff.mp hrat with hpos | hneg
      · exact hpos.1
      · exfalso
        linarith [hv r, hneg.2]
    exact (P.positive_iff r s).mp hprofile
  · intro hreact
    have hratio : 0 < rationalLiftRatio P v s r :=
      div_pos (P.positive_of_reactant r s hreact) (hv r)
    have hbaseRat : (0 : ℚ) < rationalLiftBaseExponent P v s r := by
      rw [hcast]
      exact mul_pos hdenPos hratio
    exact_mod_cast hbaseRat

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem reactant_le_rationalLiftScale (Q : SourceNetwork Species Reaction)
    (s : Species) (r : Reaction) : Q.reactant s r ≤ rationalLiftScale Q := by
  classical
  have hrow : Q.reactant s r ≤ ∑ q : Reaction, Q.reactant s q :=
    Finset.single_le_sum
      (fun q (_hq : q ∈ (Finset.univ : Finset Reaction)) =>
        Nat.zero_le (Q.reactant s q))
      (Finset.mem_univ r)
  have hall : (∑ q : Reaction, Q.reactant s q) ≤
      ∑ t : Species, ∑ q : Reaction, Q.reactant t q :=
    Finset.single_le_sum
      (fun t (_ht : t ∈ (Finset.univ : Finset Species)) =>
        Nat.zero_le (∑ q : Reaction, Q.reactant t q))
      (Finset.mem_univ s)
  unfold rationalLiftScale
  omega

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem rationalLiftExponent_dominates (P : RationalReactivityProfile Q)
    (v : Reaction → ℚ) (hv : ∀ r, 0 < v r) (s : Species) (r : Reaction) :
    Q.reactant s r ≤ rationalLiftExponent P v s r := by
  by_cases hreact : Q.Reactant s r
  · have hbase := (rationalLiftBaseExponent_pos_iff P v hv s r).2 hreact
    have hscale := reactant_le_rationalLiftScale Q s r
    simp only [rationalLiftExponent]
    have hone : 1 ≤ rationalLiftBaseExponent P v s r := hbase
    calc
      Q.reactant s r ≤ rationalLiftScale Q := hscale
      _ = rationalLiftScale Q * 1 := by omega
      _ ≤ rationalLiftScale Q * rationalLiftBaseExponent P v s r :=
        Nat.mul_le_mul_left _ hone
  · have hz : Q.reactant s r = 0 := Nat.eq_zero_of_not_pos hreact
    simp [hz]

/-- Stoichiometrically silent, support-preserving rational lift. -/
def rationalLiftSource (P : RationalReactivityProfile Q) (v : Reaction → ℚ)
    (hv : ∀ r, 0 < v r) :
    SourceNetwork Species Reaction where
  reactant := rationalLiftExponent P v
  product := fun s r => Q.product s r +
    (rationalLiftExponent P v s r - Q.reactant s r)
  catalyst := fun s r => Q.catalyst s r +
    (rationalLiftExponent P v s r - Q.reactant s r)
  catalyst_le_reactant := by
    intro s r
    have hle := rationalLiftExponent_dominates P v hv s r
    have hold := Q.catalyst_le_reactant s r
    omega
  catalyst_le_product := by
    intro s r
    exact Nat.add_le_add_right (Q.catalyst_le_product s r) _

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem rationalLiftSource_stoich_eq (P : RationalReactivityProfile Q)
    (v : Reaction → ℚ) (hv : ∀ r, 0 < v r) :
    (rationalLiftSource P v hv).stoich = Q.stoich := by
  ext s r
  have hdom := rationalLiftExponent_dominates P v hv s r
  simp [SourceNetwork.stoich, rationalLiftSource, Nat.cast_add,
    Nat.cast_sub hdom]
  ring_nf

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem rationalLiftSource_reactant_iff (P : RationalReactivityProfile Q)
    (v : Reaction → ℚ) (hv : ∀ r, 0 < v r) (s : Species) (r : Reaction) :
    (rationalLiftSource P v hv).Reactant s r ↔ Q.Reactant s r := by
  change 0 < rationalLiftExponent P v s r ↔ Q.Reactant s r
  simp only [rationalLiftExponent]
  have hscale : 0 < rationalLiftScale Q := by simp [rationalLiftScale]
  constructor
  · intro hprod
    have hbase : 0 < rationalLiftBaseExponent P v s r := by
      by_contra hnot
      have hz : rationalLiftBaseExponent P v s r = 0 := Nat.eq_zero_of_not_pos hnot
      simp [hz] at hprod
    exact (rationalLiftBaseExponent_pos_iff P v hv s r).1 hbase
  · intro hreact
    exact Nat.mul_pos hscale
      ((rationalLiftBaseExponent_pos_iff P v hv s r).2 hreact)

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem rationalLiftExponent_flux_div_concentration
    (P : RationalReactivityProfile Q) (v : Reaction → ℚ)
    (hv : ∀ r, 0 < v r) (s : Species) (r : Reaction) :
    (rationalLiftExponent P v s r : ℚ) * v r /
        (rationalLiftScale Q * (rationalLiftRatio P v).den : ℕ) =
      P.value r s := by
  have hdenPos : (0 : ℚ) < (rationalLiftRatio P v).den := by
    exact_mod_cast Nat.pos_of_ne_zero (rationalLiftRatio P v).den_ne_zero
  have hscalePos : (0 : ℚ) < rationalLiftScale Q := by
    exact_mod_cast (show 0 < rationalLiftScale Q by simp [rationalLiftScale])
  rw [show (rationalLiftExponent P v s r : ℚ) =
      (rationalLiftScale Q : ℚ) * rationalLiftBaseExponent P v s r by
        simp [rationalLiftExponent]]
  rw [rationalLiftBaseExponent_cast P v hv s r]
  simp only [rationalLiftRatio, Nat.cast_mul]
  field_simp [ne_of_gt (hv r), ne_of_gt hdenPos, ne_of_gt hscalePos]

/-- The denominator-clearing concentration, chosen uniformly across species. -/
noncomputable def rationalLiftConcentration
    (P : RationalReactivityProfile Q) (v : Reaction → ℚ) : Species → ℝ :=
  fun _ => ((rationalLiftScale Q * (rationalLiftRatio P v).den : ℕ) : ℝ)

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem rationalLiftConcentration_pos
    (P : RationalReactivityProfile Q) (v : Reaction → ℚ) (s : Species) :
    0 < rationalLiftConcentration P v s := by
  have hscale : 0 < rationalLiftScale Q := by simp [rationalLiftScale]
  have hden : 0 < (rationalLiftRatio P v).den :=
    Nat.pos_of_ne_zero (rationalLiftRatio P v).den_ne_zero
  change 0 < (((rationalLiftScale Q * (rationalLiftRatio P v).den : ℕ)) : ℝ)
  exact_mod_cast Nat.mul_pos hscale hden

/-- The rational profile, cast to reals and authenticated against the lifted
literal support. -/
noncomputable def rationalLiftReactivity
    (P : RationalReactivityProfile Q) (v : Reaction → ℚ)
    (hv : ∀ r, 0 < v r) : Reactivity (rationalLiftSource P v hv) where
  value := fun r s => (P.value r s : ℝ)
  nonneg := by intro r s; exact_mod_cast P.nonneg r s
  positive_of_reactant := by
    intro r s h
    exact_mod_cast P.positive_of_reactant r s
      ((rationalLiftSource_reactant_iff P v hv s r).mp h)
  zero_of_not_reactant := by
    intro r s h
    exact_mod_cast P.zero_of_not_reactant r s
      (fun hold => h ((rationalLiftSource_reactant_iff P v hv s r).mpr hold))

/-- The exact ordinary mass-action realization obtained from the reconstructed
positive rate constants. -/
noncomputable def rationalLiftMassActionInstance
    (P : RationalReactivityProfile Q) (v : Reaction → ℚ)
    (hv : ∀ r, 0 < v r) : ClassicalMassActionInstance (rationalLiftSource P v hv) where
  concentration := rationalLiftConcentration P v
  rateConstant := reconstructedRate (rationalLiftSource P v hv)
    (rationalLiftConcentration P v) (fun r => (v r : ℝ))
  concentration_pos := rationalLiftConcentration_pos P v
  rateConstant_pos := reconstructedRate_pos _ _ _
    (rationalLiftConcentration_pos P v) (by intro r; exact_mod_cast hv r)
  reactivity := rationalLiftReactivity P v hv
  derivative_formula := by
    intro r s
    change (P.value r s : ℝ) =
      (rationalLiftExponent P v s r : ℝ) *
        (reconstructedRate (rationalLiftSource P v hv)
          (rationalLiftConcentration P v) (fun q => (v q : ℝ)) r *
          massActionMonomial (rationalLiftSource P v hv)
            (rationalLiftConcentration P v) r) /
        rationalLiftConcentration P v s
    rw [reconstructedRate_mul_monomial _ _ _
      (rationalLiftConcentration_pos P v) r]
    have hrat := rationalLiftExponent_flux_div_concentration P v hv s r
    unfold rationalLiftConcentration
    exact_mod_cast hrat.symm

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem rationalLift_reactionFlux_eq
    (P : RationalReactivityProfile Q) (v : Reaction → ℚ)
    (hv : ∀ r, 0 < v r) (r : Reaction) :
    classicalReactionFlux (rationalLiftMassActionInstance P v hv) r = (v r : ℝ) := by
  change reconstructedRate (rationalLiftSource P v hv)
      (rationalLiftConcentration P v) (fun q => (v q : ℝ)) r *
      massActionMonomial (rationalLiftSource P v hv)
        (rationalLiftConcentration P v) r = (v r : ℝ)
  exact reconstructedRate_mul_monomial _ _ _
    (rationalLiftConcentration_pos P v) r

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem rationalLift_stationary
    (P : RationalReactivityProfile Q) (v : Reaction → ℚ)
    (hv : ∀ r, 0 < v r)
    (hker : ∀ s, ∑ r : Reaction, (Q.stoich s r : ℚ) * v r = 0) :
    ClassicalStationary (rationalLiftMassActionInstance P v hv) := by
  intro s
  simp_rw [rationalLift_reactionFlux_eq P v hv]
  rw [rationalLiftSource_stoich_eq P v hv]
  exact_mod_cast hker s

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem rationalLift_jacobian_eq
    (P : RationalReactivityProfile Q) (v : Reaction → ℚ)
    (hv : ∀ r, 0 < v r) :
    (rationalLiftSource P v hv).jacobian (rationalLiftReactivity P v hv) =
      Q.jacobian P.toReactivity := by
  ext i j
  simp only [SourceNetwork.jacobian, rationalLiftReactivity,
    RationalReactivityProfile.toReactivity]
  rw [rationalLiftSource_stoich_eq P v hv]

omit [DecidableEq Species] [DecidableEq Reaction] in
/-- **General support-preserving rational lifting theorem.**  Every positive
rational stationary flux and every rational admissible reactivity profile are
realized exactly by classical mass action on a catalytic padding of the source.
The lift preserves the complete stoichiometric matrix and literal reactant
support, hence preserves every child-selection matrix. -/
theorem rationalReactivity_realizable_by_supportPreservingPadding
    (Q : SourceNetwork Species Reaction)
    (P : RationalReactivityProfile Q) (v : Reaction → ℚ)
    (hv : ∀ r, 0 < v r)
    (hker : ∀ s, ∑ r : Reaction, (Q.stoich s r : ℚ) * v r = 0) :
    ∃ (Qlift : SourceNetwork Species Reaction)
      (M : ClassicalMassActionInstance Qlift),
      Qlift.stoich = Q.stoich ∧
      (∀ s r, Qlift.Reactant s r ↔ Q.Reactant s r) ∧
      ClassicalStationary M ∧
      Qlift.jacobian M.reactivity = Q.jacobian P.toReactivity := by
  refine ⟨rationalLiftSource P v hv, rationalLiftMassActionInstance P v hv,
    rationalLiftSource_stoich_eq P v hv, ?_, rationalLift_stationary P v hv hker,
    rationalLift_jacobian_eq P v hv⟩
  exact rationalLiftSource_reactant_iff P v hv

end Construction

end DUnstableCores
