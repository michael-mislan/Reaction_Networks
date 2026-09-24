import proofs.PowerLawSmallRAF.FiniteLigationExposure

namespace PowerLawSmallRAF

open scoped BigOperators

/-- A full row is sampled before knowing which coordinates will be usable. -/
noncomputable def bernoulliFullRowWeight {I : Type*} [Fintype I]
    (p : ℝ) (cfg : I → Bool) : ℝ := ∏ i, bernoulliBitWeight p (cfg i)

theorem sum_bernoulliFullRowWeight {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ) :
    (∑ cfg : I → Bool, bernoulliFullRowWeight p cfg) = 1 := by
  classical
  unfold bernoulliFullRowWeight
  rw [← Fintype.prod_sum (fun (_ : I) (b : Bool) => bernoulliBitWeight p b)]
  simp [bernoulliBitWeight]

theorem bernoulliFullRow_subset_false_mass {I : Type*} [Fintype I] [DecidableEq I]
    (p : ℝ) (s : Finset I) :
    (∑ cfg : I → Bool,
      if ∀ i ∈ s, cfg i = false then bernoulliFullRowWeight p cfg else 0) =
        (1 - p)^s.card := by
  classical
  have hpoint : ∀ cfg : I → Bool,
      (if ∀ i ∈ s, cfg i = false then bernoulliFullRowWeight p cfg else 0) =
        ∏ i, if i ∈ s then
          (if cfg i = false then bernoulliBitWeight p (cfg i) else 0)
          else bernoulliBitWeight p (cfg i) := by
    intro cfg
    by_cases h : ∀ i ∈ s, cfg i = false
    · rw [if_pos h]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ s
      · simp only [hi, h i hi, ↓reduceIte]
      · simp only [hi, ↓reduceIte]
    · rw [if_neg h]
      push Not at h
      obtain ⟨i, hi, hb⟩ := h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [if_pos hi, if_neg hb]
  simp_rw [hpoint]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) =>
    if i ∈ s then (if b = false then bernoulliBitWeight p b else 0)
      else bernoulliBitWeight p b)]
  have hsum : ∀ i : I,
      (∑ b : Bool, if i ∈ s then (if b = false then bernoulliBitWeight p b else 0)
        else bernoulliBitWeight p b) = if i ∈ s then 1-p else 1 := by
    intro i
    by_cases hi : i ∈ s <;> simp [hi, bernoulliBitWeight]
  simp_rw [hsum]
  rw [Finset.prod_ite_mem_eq]
  simp

theorem bernoulliFullRow_subset_choice {I : Type*} [Fintype I] [DecidableEq I]
    (p : ℝ) (s : Finset I) (onFalse onHit : ℝ) :
    (∑ cfg : I → Bool, bernoulliFullRowWeight p cfg *
      (if ∀ i ∈ s, cfg i = false then onFalse else onHit)) =
      (1-p)^s.card * onFalse + (1-(1-p)^s.card) * onHit := by
  classical
  have hpoint : ∀ cfg : I → Bool,
      bernoulliFullRowWeight p cfg * (if ∀ i ∈ s, cfg i = false then onFalse else onHit) =
        (if ∀ i ∈ s, cfg i = false then bernoulliFullRowWeight p cfg else 0) * onFalse +
        (bernoulliFullRowWeight p cfg -
          (if ∀ i ∈ s, cfg i = false then bernoulliFullRowWeight p cfg else 0)) * onHit := by
    intro cfg
    split_ifs <;> ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_sub_distrib,
    bernoulliFullRow_subset_false_mass, sum_bernoulliFullRowWeight]

def availableFullRowCuts (known : Finset LigationWord) (w : LigationWord) :
    Finset (ligationCuts w) := Finset.univ.filter fun i => i.val ∈ availableLigationCuts known w

theorem availableFullRowCuts_card (known : Finset LigationWord) (w : LigationWord) :
    (availableFullRowCuts known w).card = (availableLigationCuts known w).card := by
  classical
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i _ j _ h
    exact Subtype.ext h
  · intro i hi
    have hcut : i ∈ ligationCuts w := (Finset.mem_filter.mp hi).1
    exact ⟨⟨i, hcut⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

def fullLigationRowFails (known : Finset LigationWord) (w : LigationWord)
    (cfg : (ligationCuts w) → Bool) : Prop :=
  ∀ i ∈ availableFullRowCuts known w, cfg i = false

noncomputable instance (known : Finset LigationWord) (w : LigationWord)
    (cfg : (ligationCuts w) → Bool) : Decidable (fullLigationRowFails known w cfg) :=
  inferInstanceAs (Decidable (∀ i ∈ availableFullRowCuts known w, cfg i = false))

/-- Integrating a static full split-position row gives exactly the generation
kernel, including coordinates whose reactants were not generated. -/
theorem fullLigationRow_choice (p : ℝ) (known : Finset LigationWord) (w : LigationWord)
    (onFalse onHit : ℝ) :
    (∑ cfg : (ligationCuts w) → Bool, bernoulliFullRowWeight p cfg *
      (if fullLigationRowFails known w cfg then onFalse else onHit)) =
      ligationFailureChance p known w * onFalse +
        (1 - ligationFailureChance p known w) * onHit := by
  classical
  have h := bernoulliFullRow_subset_choice p (availableFullRowCuts known w) onFalse onHit
  rw [availableFullRowCuts_card] at h
  convert h using 1

end PowerLawSmallRAF
