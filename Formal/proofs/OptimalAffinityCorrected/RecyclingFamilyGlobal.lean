import proofs.OptimalAffinityCorrected.RecyclingFamily

namespace OptimalAffinityCorrected

open scoped BigOperators
noncomputable section

def weightedGeom (n : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (k + 1 : ℕ) * y ^ k

theorem weightedGeom_identity (n : ℕ) (y : ℝ) :
    (y - 1) * weightedGeom n y =
      (n + 1 : ℕ) * y ^ n - ∑ k ∈ Finset.range (n + 1), y ^ k := by
  induction n with
  | zero => simp [weightedGeom]
  | succ n ih =>
      simp only [weightedGeom, Finset.sum_range_succ, Nat.cast_add,
        Nat.cast_one, pow_succ]
      simp only [weightedGeom, Finset.sum_range_succ] at ih
      push_cast at ih
      rw [mul_add]
      rw [ih]
      ring

theorem geomSum_identity (n : ℕ) (y : ℝ) :
    (y - 1) * (∑ k ∈ Finset.range n, y ^ k) = y ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

def familyD (m : ℕ) (r : ℝ) : ℝ := (m : ℝ) / (r * (2 - r))
def familyd (m : ℕ) (r : ℝ) : ℝ := r * m / (2 - r)
def familyc (m : ℕ) (r : ℝ) : ℝ := familyd m r + 1

def familyH (m : ℕ) (r J y : ℝ) : ℝ :=
  y ^ (m - 1) *
    (familyc m r * y - familyD m r * (y + (r - 1) * J) ^ 2)

theorem family_H1_certificate (m : ℕ) (hm : 1 ≤ m)
    (r y : ℝ) (hr0 : r ≠ 0) (hr2 : r ≠ 2) :
    1 - familyH m r 1 y =
      (y - 1) ^ 2 *
        (familyD m r * y ^ (m - 1) + weightedGeom (m - 1) y) := by
  have hmpos : 0 < m := Nat.zero_lt_of_lt hm
  have hmpred : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hmpos
  have hgeom := weightedGeom_identity (m - 1) y
  rw [hmpred] at hgeom
  have hsum := geomSum_identity m y
  rw [← hmpred, pow_succ] at hsum
  rw [hmpred] at hsum
  have hgeom_mul := congrArg (fun z : ℝ => (y - 1) * z) hgeom
  unfold familyH familyc familyd familyD
  field_simp [hr0, hr2]
  ring_nf at hgeom_mul hsum ⊢
  linear_combination -(r * (2 - r)) * hgeom_mul +
    (r * (2 - r)) * hsum

theorem family_HJ_gap (m : ℕ) (r J y : ℝ) :
    familyH m r 1 y - familyH m r J y =
      familyD m r * y ^ (m - 1) * (r - 1) * (J - 1) *
        (2 * y + (r - 1) * (J + 1)) := by
  unfold familyH
  ring

theorem weightedGeom_nonneg (n : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ weightedGeom n y := by
  unfold weightedGeom
  positivity

theorem family_H1_le_one (m : ℕ) (hm : 1 ≤ m)
    (r y : ℝ) (hr1 : 1 < r) (hr2 : r < 2) (hy : 0 < y) :
    familyH m r 1 y ≤ 1 := by
  have hr0 : r ≠ 0 := by linarith
  have hrne2 : r ≠ 2 := by linarith
  have hD : 0 < familyD m r := by
    unfold familyD
    positivity
  have hpow : 0 < y ^ (m - 1) := pow_pos hy _
  have hW : 0 ≤ weightedGeom (m - 1) y :=
    weightedGeom_nonneg (m - 1) y (le_of_lt hy)
  have hbracket : 0 < familyD m r * y ^ (m - 1) +
      weightedGeom (m - 1) y := by positivity
  have hcert := family_H1_certificate m hm r y hr0 hrne2
  nlinarith [sq_nonneg (y - 1)]

theorem family_H1_eq_one_iff (m : ℕ) (hm : 1 ≤ m)
    (r y : ℝ) (hr1 : 1 < r) (hr2 : r < 2) (hy : 0 < y) :
    familyH m r 1 y = 1 ↔ y = 1 := by
  have hr0 : r ≠ 0 := by linarith
  have hrne2 : r ≠ 2 := by linarith
  have hD : 0 < familyD m r := by
    unfold familyD
    positivity
  have hpow : 0 < y ^ (m - 1) := pow_pos hy _
  have hW : 0 ≤ weightedGeom (m - 1) y :=
    weightedGeom_nonneg (m - 1) y (le_of_lt hy)
  have hbracket : 0 < familyD m r * y ^ (m - 1) +
      weightedGeom (m - 1) y := by positivity
  constructor
  · intro heq
    have hcert := family_H1_certificate m hm r y hr0 hrne2
    have hsquare : (y - 1) ^ 2 = 0 := by nlinarith
    nlinarith [sq_nonneg (y - 1)]
  · rintro rfl
    norm_num [familyH, familyc, familyd, familyD]
    field_simp [hr0, hrne2]
    ring

def familyJ1 (r x y : ℝ) : ℝ := (r * x - y) / (r - 1)

def familyJ2 (m : ℕ) (r x y : ℝ) : ℝ :=
  familyc m r * y ^ m - familyd m r * x ^ 2 * y ^ (m - 1)

def FamilySteady (m : ℕ) (r x y : ℝ) : Prop :=
  familyJ1 r x y = familyJ2 m r x y

def FamilyUniqueGlobalMaximum (m : ℕ) (r : ℝ) : Prop :=
  FamilySteady m r 1 1 ∧
  (∀ x y : ℝ, 0 < x → 0 < y → FamilySteady m r x y →
    familyJ1 r x y ≤ familyJ1 r 1 1) ∧
  (∀ x y : ℝ, 0 < x → 0 < y → FamilySteady m r x y →
    familyJ1 r x y = familyJ1 r 1 1 → x = 1 ∧ y = 1)

theorem familyJ1_elimination (r x y : ℝ) (hr1 : r ≠ 1) :
    y + (r - 1) * familyJ1 r x y = r * x := by
  unfold familyJ1
  field_simp [hr1]
  ring

theorem familyJ2_eq_familyH (m : ℕ) (hm : 1 ≤ m)
    (r x y : ℝ) (hr1 : r ≠ 1) (hr2 : r ≠ 2) :
    familyJ2 m r x y = familyH m r (familyJ1 r x y) y := by
  have hmpos : 0 < m := Nat.zero_lt_of_lt hm
  have hmpred : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hmpos
  have hpow : y ^ m = y ^ (m - 1) * y := by
    exact (congrArg (fun n : ℕ => y ^ n) hmpred).symm.trans
      (pow_succ y (m - 1))
  have helim := familyJ1_elimination r x y hr1
  unfold familyJ2 familyH
  rw [helim]
  unfold familyc familyd familyD
  rw [hpow]
  field_simp [hr2]

theorem familySteady_reduced (m : ℕ) (hm : 1 ≤ m)
    (r x y : ℝ) (hr1 : r ≠ 1) (hr2 : r ≠ 2)
    (hs : FamilySteady m r x y) :
    familyJ1 r x y = familyH m r (familyJ1 r x y) y := by
  rw [← familyJ2_eq_familyH m hm r x y hr1 hr2]
  exact hs

theorem family_current_le_one (m : ℕ) (hm : 1 ≤ m)
    (r x y : ℝ) (hr1 : 1 < r) (hr2 : r < 2)
    (hy : 0 < y) (hs : FamilySteady m r x y) :
    familyJ1 r x y ≤ 1 := by
  have hrne1 : r ≠ 1 := by linarith
  have hrne2 : r ≠ 2 := by linarith
  have hred := familySteady_reduced m hm r x y hrne1 hrne2 hs
  by_contra hle
  have hJ : 1 < familyJ1 r x y := lt_of_not_ge hle
  have hD : 0 < familyD m r := by
    unfold familyD
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
    positivity
  have hpow : 0 < y ^ (m - 1) := pow_pos hy _
  have hlast : 0 < 2 * y + (r - 1) * (familyJ1 r x y + 1) := by
    positivity
  have hgap := family_HJ_gap m r (familyJ1 r x y) y
  have hgapPos : 0 < familyH m r 1 y -
      familyH m r (familyJ1 r x y) y := by
    rw [hgap]
    positivity
  have hH1 := family_H1_le_one m hm r y hr1 hr2 hy
  linarith

theorem family_current_eq_one_unique (m : ℕ) (hm : 1 ≤ m)
    (r x y : ℝ) (hr1 : 1 < r) (hr2 : r < 2)
    (hy : 0 < y) (hs : FamilySteady m r x y)
    (heq : familyJ1 r x y = 1) : x = 1 ∧ y = 1 := by
  have hrne1 : r ≠ 1 := by linarith
  have hrne2 : r ≠ 2 := by linarith
  have hred := familySteady_reduced m hm r x y hrne1 hrne2 hs
  have hHy : familyH m r 1 y = 1 := by simpa [heq] using hred.symm
  have hy1 := (family_H1_eq_one_iff m hm r y hr1 hr2 hy).mp hHy
  have hdiv := (div_eq_iff (sub_ne_zero.mpr hrne1)).mp heq
  constructor
  · rw [hy1] at hdiv
    nlinarith
  · exact hy1

theorem family_unit_steady (m : ℕ) (r : ℝ) (hr1 : r ≠ 1)
    (hr2 : r ≠ 2) : FamilySteady m r 1 1 := by
  unfold FamilySteady familyJ1 familyJ2 familyc familyd
  simp only [one_pow, mul_one]
  field_simp [hr1, hr2]
  ring

theorem family_uniqueGlobalMaximum (m : ℕ) (hm : 2 ≤ m)
    (r : ℝ) (hr1 : 1 < r) (hr2 : r < 2) :
    FamilyUniqueGlobalMaximum m r := by
  have hm1 : 1 ≤ m := le_trans (by omega) hm
  have hrne1 : r ≠ 1 := by linarith
  have hrne2 : r ≠ 2 := by linarith
  have hunitJ : familyJ1 r 1 1 = 1 := by
    unfold familyJ1
    field_simp [hrne1]
  refine ⟨family_unit_steady m r hrne1 hrne2, ?_, ?_⟩
  · intro x y hx hy hs
    rw [hunitJ]
    exact family_current_le_one m hm1 r x y hr1 hr2 hy hs
  · intro x y hx hy hs heq
    rw [hunitJ] at heq
    exact family_current_eq_one_unique m hm1 r x y hr1 hr2 hy hs heq

def IntegerRecyclingSourceCertificate (m : ℕ) : Prop :=
  let mr : ℝ := m
  let r := 1 + 1 / mr
  2 ≤ m ∧
  1 < r ∧ r < 2 ∧
  (0 : ℝ) < r / (r - 1) ∧
  (0 : ℝ) < 1 / (r - 1) ∧
  (0 : ℝ) < familyd m r ∧
  (0 : ℝ) < familyc m r ∧
  FamilyUniqueGlobalMaximum m r ∧
  recyclingFamilyExpAffinity mr r = 1 + 2 / mr - 1 / mr ^ 2 ∧
  recyclingFamilyExpAffinity mr r < 2

theorem integerRecyclingSourceCertificate (m : ℕ) (hm : 2 ≤ m) :
    IntegerRecyclingSourceCertificate m := by
  dsimp [IntegerRecyclingSourceCertificate]
  rcases integerRecyclingFamily_exactData m hm with
    ⟨hr1, hr2, hk1p, hk1m, hk2m, haff, hlt2⟩
  have hk2p : 0 < familyc m (1 + 1 / (m : ℝ)) := by
    unfold familyc familyd
    positivity
  refine ⟨hm, hr1, hr2, hk1p, hk1m, ?_, hk2p, ?_, haff, hlt2⟩
  · simpa [familyd] using hk2m
  · exact family_uniqueGlobalMaximum m hm (1 + 1 / (m : ℝ)) hr1 hr2

theorem noUniformPositiveSourceAffinityGap :
    ∀ ε : ℝ, 0 < ε →
      ∃ m : ℕ, IntegerRecyclingSourceCertificate m ∧
        let r := 1 + 1 / (m : ℝ)
        1 < recyclingFamilyExpAffinity (m : ℝ) r ∧
        recyclingFamilyExpAffinity (m : ℝ) r < 1 + ε ∧
        recyclingFamilyExpAffinity (m : ℝ) r < 2 := by
  intro ε hε
  rcases noUniformPositiveAffinityGap ε hε with
    ⟨m, hm, hgt1, hltε, hlt2⟩
  exact ⟨m, integerRecyclingSourceCertificate m hm, hgt1, hltε, hlt2⟩

end
end OptimalAffinityCorrected
