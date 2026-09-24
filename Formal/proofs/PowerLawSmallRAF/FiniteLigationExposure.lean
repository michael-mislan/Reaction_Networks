import Mathlib

namespace PowerLawSmallRAF

open scoped BigOperators

abbrev LigationWord := List Bool

def ligationCuts (w : LigationWord) : Finset Nat := Finset.Ioo 0 w.length

def availableLigationCuts (known : Finset LigationWord) (w : LigationWord) : Finset Nat :=
  (ligationCuts w).filter fun i => w.take i ∈ known ∧ w.drop i ∈ known

def missingPrefixCuts (known : Finset LigationWord) (w : LigationWord) : Finset Nat :=
  (ligationCuts w).filter fun i => w.take i ∉ known

def missingSuffixCuts (known : Finset LigationWord) (w : LigationWord) : Finset Nat :=
  (ligationCuts w).filter fun i => w.drop i ∉ known

def LigationCutDensity (known : Finset LigationWord) (w : LigationWord) : Prop :=
  8 * (missingPrefixCuts known w).card ≤ w.length ∧
    8 * (missingSuffixCuts known w).card ≤ w.length

instance (known : Finset LigationWord) (w : LigationWord) :
    Decidable (LigationCutDensity known w) := inferInstanceAs (Decidable (_ ∧ _))

theorem ligationCuts_card_le_parts (known : Finset LigationWord) (w : LigationWord) :
    w.length - 1 ≤ (availableLigationCuts known w).card +
      (missingPrefixCuts known w).card + (missingSuffixCuts known w).card := by
  have hsub : ligationCuts w ⊆
      (availableLigationCuts known w ∪ missingPrefixCuts known w) ∪
        missingSuffixCuts known w := by
    intro i hi
    by_cases hp : w.take i ∈ known
    · by_cases hs : w.drop i ∈ known
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hi, hp, hs⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, hs⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hi, hp⟩))
  have hcard := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  simpa [ligationCuts] using hcard

/-- Prefix and suffix failures need not be independent. A union bound on their
positions alone supplies at least half of the literal split positions. -/
theorem LigationCutDensity.half_length_le_available
    {known : Finset LigationWord} {w : LigationWord}
    (hd : LigationCutDensity known w) (hlen : 4 ≤ w.length) :
    w.length ≤ 2 * (availableLigationCuts known w).card := by
  have hparts := ligationCuts_card_le_parts known w
  obtain ⟨hp, hs⟩ := hd
  omega

def bernoulliBitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

theorem sum_bernoulliBitWeight (p : ℝ) : ∑ b : Bool, bernoulliBitWeight p b = 1 := by
  simp [bernoulliBitWeight]

/-- Exact mass of missing every coordinate in an independent finite Bernoulli
row. At a word-generation step the row is its currently valid split positions. -/
theorem finite_bernoulli_all_false_mass {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ) :
    (∑ cfg : I → Bool,
      if ∀ i, cfg i = false then ∏ i, bernoulliBitWeight p (cfg i) else 0) =
        (1 - p) ^ Fintype.card I := by
  classical
  have hpoint : ∀ cfg : I → Bool,
      (if ∀ i, cfg i = false then ∏ i, bernoulliBitWeight p (cfg i) else 0) =
      ∏ i, if cfg i = false then bernoulliBitWeight p (cfg i) else 0 := by
    intro cfg
    by_cases h : ∀ i, cfg i = false
    · simp [h]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      rw [if_neg h]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  simp_rw [hpoint]
  rw [← Fintype.prod_sum (fun (_ : I) (b : Bool) =>
    if b = false then bernoulliBitWeight p b else 0)]
  simp [bernoulliBitWeight]

def ligationFailureChance (p : ℝ) (known : Finset LigationWord) (w : LigationWord) : ℝ :=
  (1 - p) ^ (availableLigationCuts known w).card

theorem ligationFailureChance_exact (p : ℝ)
    (known : Finset LigationWord) (w : LigationWord) :
    (∑ cfg : (availableLigationCuts known w) → Bool,
      if ∀ i, cfg i = false then ∏ i, bernoulliBitWeight p (cfg i) else 0) =
      ligationFailureChance p known w := by
  rw [finite_bernoulli_all_false_mass]
  simp [ligationFailureChance]

theorem ligationFailureChance_nonneg_le_one {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (known : Finset LigationWord) (w : LigationWord) :
    0 ≤ ligationFailureChance p known w ∧ ligationFailureChance p known w ≤ 1 := by
  constructor
  · exact pow_nonneg (sub_nonneg.mpr hp1) _
  · exact pow_le_one₀ (sub_nonneg.mpr hp1) (by linarith)

theorem ligationFailureChance_le_exp {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {known : Finset LigationWord} {w : LigationWord}
    (hd : LigationCutDensity known w) (hlen : 4 ≤ w.length) :
    ligationFailureChance p known w ≤ Real.exp (-p * (w.length : ℝ) / 2) := by
  have hc : (w.length : ℝ) ≤ 2 * (availableLigationCuts known w).card := by
    exact_mod_cast hd.half_length_le_available hlen
  calc
    ligationFailureChance p known w ≤
        (Real.exp (-p)) ^ (availableLigationCuts known w).card :=
      pow_le_pow_left₀ (sub_nonneg.mpr hp1) (Real.one_sub_le_exp_neg p) _
    _ = Real.exp ((availableLigationCuts known w).card * (-p)) := by
      rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (-p * (w.length : ℝ) / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hp (sub_nonneg.mpr hc)]

/-- Mass of a sequential word-generation experiment restricted to
density-qualified failures at selected words. Unselected words undergo the
ordinary generation step. A source interpretation uses a distinct,
length-ordered word schedule, so each word's split row is fresh. -/
noncomputable def stoppedLigationMass (p : ℝ) (selected : Finset LigationWord) :
    List LigationWord → Finset LigationWord → ℝ
  | [], _ => 1
  | w :: rest, known =>
      if w ∈ selected then
        if LigationCutDensity known w then
          ligationFailureChance p known w * stoppedLigationMass p selected rest known
        else 0
      else
        ligationFailureChance p known w * stoppedLigationMass p selected rest known +
        (1 - ligationFailureChance p known w) *
          stoppedLigationMass p selected rest (insert w known)

def selectedWordLengthSum (selected : Finset LigationWord) : List LigationWord → Nat
  | [] => 0
  | w :: rest => (if w ∈ selected then w.length else 0) + selectedWordLengthSum selected rest

/-- The stopped product estimate for the concrete Bernoulli word-generation
kernel. Its exponent retains every selected word length. The later target
bound selects prefixes or suffixes of distinct lengths. -/
theorem stoppedLigationMass_le_exp {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (selected : Finset LigationWord) (words : List LigationWord)
    (hlen : ∀ w ∈ words, w ∈ selected → 4 ≤ w.length)
    (known : Finset LigationWord) :
    stoppedLigationMass p selected words known ≤
      Real.exp (-p * (selectedWordLengthSum selected words : ℝ) / 2) := by
  induction words generalizing known with
  | nil => simp [stoppedLigationMass, selectedWordLengthSum]
  | cons w rest ih =>
      have hrest : ∀ v ∈ rest, v ∈ selected → 4 ≤ v.length := by
        intro v hv hs
        exact hlen v (List.mem_cons_of_mem w hv) hs
      have hi0 := ih hrest known
      have hi1 := ih hrest (insert w known)
      have hm := ligationFailureChance_nonneg_le_one hp hp1 known w
      by_cases hs : w ∈ selected
      · simp only [stoppedLigationMass, if_pos hs, selectedWordLengthSum]
        by_cases hd : LigationCutDensity known w
        · rw [if_pos hd]
          calc
            ligationFailureChance p known w * stoppedLigationMass p selected rest known ≤
                ligationFailureChance p known w *
                  Real.exp (-p * (selectedWordLengthSum selected rest : ℝ) / 2) :=
              mul_le_mul_of_nonneg_left hi0 hm.1
            _ ≤ Real.exp (-p * (w.length : ℝ) / 2) *
                  Real.exp (-p * (selectedWordLengthSum selected rest : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right
                (ligationFailureChance_le_exp hp hp1 hd (hlen w (by simp) hs))
                (Real.exp_nonneg _)
            _ = Real.exp (-p * ((w.length + selectedWordLengthSum selected rest : Nat) : ℝ) / 2) := by
              rw [← Real.exp_add]
              congr 1
              push_cast
              ring
        · rw [if_neg hd]
          exact Real.exp_nonneg _
      · simp only [stoppedLigationMass, if_neg hs, selectedWordLengthSum, zero_add]
        calc
          _ ≤ ligationFailureChance p known w *
                Real.exp (-p * (selectedWordLengthSum selected rest : ℝ) / 2) +
              (1 - ligationFailureChance p known w) *
                Real.exp (-p * (selectedWordLengthSum selected rest : ℝ) / 2) :=
            add_le_add (mul_le_mul_of_nonneg_left hi0 hm.1)
              (mul_le_mul_of_nonneg_left hi1 (sub_nonneg.mpr hm.2))
          _ = _ := by ring

end PowerLawSmallRAF
