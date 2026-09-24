import proofs.RandomViability.SingleIncidenceMassDefect

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 30000

def ProductiveSingletonIncidence {n : ℕ} (r : Reaction n) (z : Molecule n) : Prop :=
  molLength (reactionLeft r) ≤ 2 ∧ molLength (reactionRight r) ≤ 2 ∧
    2 < molLength (reactionProduct r) ∧ (molLength z ≤ 2 ∨ z = reactionProduct r)

def MixedFoodIncidence {n : ℕ} (r : Reaction n) : Prop :=
  (molLength (reactionLeft r) ≤ 2 ∧ 2 < molLength (reactionRight r)) ∨
  (2 < molLength (reactionLeft r) ∧ molLength (reactionRight r) ≤ 2)

def OutsiderFoodIncidence {n : ℕ} (r : Reaction n) (z : Molecule n) : Prop :=
  molLength (reactionLeft r) ≤ 2 ∧ molLength (reactionRight r) ≤ 2 ∧
    2 < molLength (reactionProduct r) ∧ 2 < molLength z ∧ z ≠ reactionProduct r

/-- Exhaustive classification of the literal reaction and catalyst, including
equal inputs and all catalyst coincidences. This is structural, not kinetic. -/
theorem local_incidence_classification {n : ℕ} (r : Reaction n) (z : Molecule n) :
    ligationNonfoodMassGain r = 0 ∨ MixedFoodIncidence r ∨ OutsiderFoodIncidence r z ∨
      ProductiveSingletonIncidence r z := by
  have hlen : molLength (reactionLeft r)+molLength (reactionRight r) =
      molLength (reactionProduct r) := by
    simpa only [molLength_reactionLeft, molLength_reactionRight, molLength_reactionProduct]
      using reaction_length_add r
  by_cases hp : molLength (reactionProduct r) ≤ 2
  · left
    have hl : molLength (reactionLeft r) ≤ 2 := by omega
    have hr : molLength (reactionRight r) ≤ 2 := by omega
    simp only [ligationNonfoodMassGain, foodMassWeight, hl, hr, hp, ↓reduceIte]
    have he : (molLength (reactionLeft r) : ℝ)+molLength (reactionRight r) =
      molLength (reactionProduct r) := by exact_mod_cast hlen
    linarith
  by_cases hl : molLength (reactionLeft r) ≤ 2
  · by_cases hr : molLength (reactionRight r) ≤ 2
    · by_cases hz : molLength z ≤ 2 ∨ z = reactionProduct r
      · exact Or.inr (Or.inr (Or.inr ⟨hl,hr,by omega,hz⟩))
      · push Not at hz
        exact Or.inr (Or.inr (Or.inl ⟨hl,hr,by omega,by omega,hz.2⟩))
    · exact Or.inr (Or.inl (Or.inl ⟨hl,by omega⟩))
  · by_cases hr : molLength (reactionRight r) ≤ 2
    · exact Or.inr (Or.inl (Or.inr ⟨by omega,hr⟩))
    · left
      simp only [ligationNonfoodMassGain, foodMassWeight, if_neg hl, if_neg hr, if_neg hp]
      norm_num

def SingleLocalIncidence {n : ℕ} (K : ℕ) (c : SourceMoleculeFibreConfig n)
    (z₀ : Molecule n) (r₀ : Reaction n) : Prop :=
  ∀ z r, molLength z ≤ K → reactionProductLength r ≤ K+2 → r ∈ c z → z = z₀ ∧ r = r₀

def eraseLocalIncidence {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (z₀ : Molecule n) (r₀ : Reaction n) : SourceMoleculeFibreConfig n :=
  fun z => if z = z₀ then (c z).erase r₀ else c z

/-- Deleting the unique local assignment removes every short incidence. The
remaining source can still contain arbitrarily many nonlocal assignments. -/
theorem erase_local_has_no_short_incidence {n K : ℕ} (c : SourceMoleculeFibreConfig n)
    (z₀ : Molecule n) (r₀ : Reaction n) (h : SingleLocalIncidence K c z₀ r₀) :
    ¬ShortIncidence K (eraseLocalIncidence c z₀ r₀) := by
  rintro ⟨z,hz,r,hr,hmem⟩
  have hzlen : molLength z ≤ K := (Finset.mem_filter.mp hz).2
  have hselected : r ∈ c z := by
    unfold eraseLocalIncidence at hmem
    split_ifs at hmem
    · exact (Finset.mem_erase.mp hmem).2
    · exact hmem
  obtain ⟨hzz,hrr⟩ := h z r hzlen hr hselected
  subst z
  subst r
  simp [eraseLocalIncidence] at hmem

end
end RandomViability
