import proofs.ThermoCoreCompatibility.CoreFamily

/-! The positive toric lift separates linear current/production inequalities
from realizability by one common species-activity vector. -/

namespace ThermoCoreCompatibility

open scoped BigOperators

variable {Species Reaction Core : Type*}
  [DecidableEq Species] [DecidableEq Reaction] [Fintype Species] [Fintype Core]

namespace ReversibleCRN

variable (Q : ReversibleCRN Species Reaction)

def activityVector (_Q : ReversibleCRN Species Reaction) (z : Species → ℝ) : Complex Species → ℝ :=
  fun c => complexActivity z c

def linearCurrent (y : Complex Species → ℝ) (r : Reaction) : ℝ :=
  Q.barrier r * (y (Q.reactant r) - y (Q.product r))

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem current_eq_linearCurrent (z : Species → ℝ) (r : Reaction) :
    Q.current z r = Q.linearCurrent (Q.activityVector z) r := rfl

def ToricRealizable (y : Complex Species → ℝ) : Prop :=
  ∃ z : Species → ℝ, (∀ s, 0 < z s) ∧ y = Q.activityVector z

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem activityVector_positive (z : Species → ℝ) (hz : ∀ s, 0 < z s) (c : Complex Species) :
    0 < Q.activityVector z c := by
  simp only [activityVector, complexActivity]
  exact Finset.prod_pos fun s _ => pow_pos (hz s) _

def NatComplexRelation (cs : Finset (Complex Species))
    (p q : Complex Species → ℕ) : Prop :=
  ∀ s, ∑ c ∈ cs, c s * p c = ∑ c ∈ cs, c s * q c

omit [DecidableEq Species] in
private theorem product_activity_pow (z : Species → ℝ) (cs : Finset (Complex Species))
    (p : Complex Species → ℕ) :
    ∏ c ∈ cs, (complexActivity z c) ^ p c =
      ∏ s : Species, z s ^ (∑ c ∈ cs, c s * p c) := by
  simp only [complexActivity]
  apply Eq.trans (Finset.prod_congr rfl fun c _ => (Finset.prod_pow Finset.univ (p c)
    (fun s => z s ^ c s)).symm)
  simp_rw [← pow_mul]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro s _
  exact Finset.prod_pow_eq_pow_sum cs (fun c => c s * p c) (z s)

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem toric_binomial_of_natComplexRelation
    (z : Species → ℝ) (cs : Finset (Complex Species))
    (p q : Complex Species → ℕ) (hrel : NatComplexRelation cs p q) :
    (∏ c ∈ cs, (Q.activityVector z c) ^ p c) =
      ∏ c ∈ cs, (Q.activityVector z c) ^ q c := by
  change (∏ c ∈ cs, (complexActivity z c) ^ p c) =
    ∏ c ∈ cs, (complexActivity z c) ^ q c
  rw [product_activity_pow, product_activity_pow]
  apply Finset.prod_congr rfl
  intro s _
  rw [hrel s]

end ReversibleCRN

namespace CoreFamily

variable {Q : ReversibleCRN Species Reaction}

/-- Compatibility after assigning an independent positive activity to every
complex. This retains barrier-weighted current magnitudes but drops the
requirement that complex activities are monomials in one species vector. -/
def LinearComplexCompatible (F : CoreFamily (Core := Core) Q) : Prop :=
  ∃ y : Complex Species → ℝ,
    (∀ c, 0 < y c) ∧
    (∀ r, 0 < (F.orientation r : ℝ) * Q.linearCurrent y r) ∧
    ∀ k, (F.core k).Productive (Q.linearCurrent y)

def PositivePolyhedralToricPoint (F : CoreFamily (Core := Core) Q) : Prop :=
  ∃ y : Complex Species → ℝ,
    Q.ToricRealizable y ∧
    (∀ r, 0 < (F.orientation r : ℝ) * Q.linearCurrent y r) ∧
    ∀ k, (F.core k).Productive (Q.linearCurrent y)

omit [DecidableEq Species] [DecidableEq Reaction] [Fintype Core] in
theorem multiCAC_iff_positivePolyhedralToricPoint (F : CoreFamily (Core := Core) Q) :
    F.MultiCAC ↔ F.PositivePolyhedralToricPoint := by
  constructor
  · rintro ⟨z, hz, horient, hprod⟩
    refine ⟨Q.activityVector z, ⟨z, hz, rfl⟩, ?_, ?_⟩
    · simpa only [Q.current_eq_linearCurrent] using horient
    · simpa only [Q.current_eq_linearCurrent] using hprod
  · rintro ⟨y, ⟨z, hz, rfl⟩, horient, hprod⟩
    refine ⟨z, hz, ?_, ?_⟩
    · simpa only [Q.current_eq_linearCurrent] using horient
    · simpa only [Q.current_eq_linearCurrent] using hprod

omit [DecidableEq Species] [DecidableEq Reaction] [Fintype Core] in
theorem multiCAC_implies_linearComplexCompatible
    (F : CoreFamily (Core := Core) Q) : F.MultiCAC → F.LinearComplexCompatible := by
  rintro ⟨z, hz, horient, hprod⟩
  refine ⟨Q.activityVector z, Q.activityVector_positive z hz, ?_, ?_⟩
  · simpa only [Q.current_eq_linearCurrent] using horient
  · simpa only [Q.current_eq_linearCurrent] using hprod

end CoreFamily

end ThermoCoreCompatibility
