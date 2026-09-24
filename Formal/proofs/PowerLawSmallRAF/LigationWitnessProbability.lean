import proofs.PowerLawSmallRAF.OrderedLigationHistory

namespace PowerLawSmallRAF

open scoped BigOperators

noncomputable def ligationHistoryEventMass (p : ℝ) (words : List LigationWord)
    (known : Finset LigationWord) (event : (Fin words.length → Bool) → Prop) : ℝ := by
  classical
  exact ∑ bits, if event bits then ligationHistoryWeight p words bits known else 0

theorem ligationHistoryEventMass_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (words : List LigationWord) (known : Finset LigationWord) (event) :
    0 ≤ ligationHistoryEventMass p words known event := by
  classical
  apply Finset.sum_nonneg
  intro bits _
  split_ifs
  · exact ligationHistoryWeight_nonneg hp hp1 words bits known
  · exact le_rfl

theorem ligationHistoryEventMass_mono {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (words : List LigationWord) (known : Finset LigationWord) (P Q)
    (h : ∀ bits, P bits → Q bits) :
    ligationHistoryEventMass p words known P ≤ ligationHistoryEventMass p words known Q := by
  classical
  apply Finset.sum_le_sum
  intro bits _
  split_ifs with hP hQ hQ
  · exact le_rfl
  · exact False.elim (hQ (h bits hP))
  · exact ligationHistoryWeight_nonneg hp hp1 words bits known
  · exact le_rfl

theorem ligationHistoryEventMass_union_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (words : List LigationWord) (known : Finset LigationWord)
    {I : Type*} (s : Finset I) (P : I → (Fin words.length → Bool) → Prop) :
    ligationHistoryEventMass p words known (fun bits => ∃ i ∈ s, P i bits) ≤
      ∑ i ∈ s, ligationHistoryEventMass p words known (P i) := by
  classical
  unfold ligationHistoryEventMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro bits _
  have hn : ∀ i ∈ s, 0 ≤ (if P i bits then ligationHistoryWeight p words bits known else 0) := by
    intro i _
    split_ifs
    · exact ligationHistoryWeight_nonneg hp hp1 words bits known
    · exact le_rfl
  split_ifs with h
  · obtain ⟨i, hi, hP⟩ := h
    have hle := Finset.single_le_sum hn hi
    simpa only [if_pos hP] using hle
  · exact Finset.sum_nonneg hn

def ligationCutCertificate (L : Nat) (w : LigationWord) (isPrefix : Bool)
    (J : Finset Nat) (known : Finset LigationWord) : Prop :=
  J ⊆ ligationCuts w ∧ w.length < 8 * J.card ∧
    ∀ i ∈ J, L < (ligationCutPart isPrefix w i).length ∧
      ligationCutPart isPrefix w i ∉ known ∧
      LigationCutDensity known (ligationCutPart isPrefix w i)

/-- Every fixed first-failure witness pays for its total selected word length.
The selected labels and split positions are fixed before the history sum. -/
theorem ligationCutCertificate_mass_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (words : List LigationWord) (hnd : words.Nodup)
    (horder : words.Pairwise (fun u v => u.length ≤ v.length))
    (known : Finset LigationWord) (L : Nat) (hL : 4 ≤ L)
    (w : LigationWord) (isPrefix : Bool) (J : Finset Nat)
    (hparts : ∀ i ∈ ligationCuts w, ligationCutPart isPrefix w i ∈ words.toFinset) :
    ligationHistoryEventMass p words known (fun bits =>
      ligationCutCertificate L w isPrefix J (ligationHistoryKnown words bits known)) ≤
      Real.exp (-p * (L : ℝ) * (w.length : ℝ) / 16) := by
  classical
  by_cases hvalid : J ⊆ ligationCuts w ∧ w.length < 8 * J.card ∧
      ∀ i ∈ J, L < (ligationCutPart isPrefix w i).length
  · let selected := J.image (ligationCutPart isPrefix w)
    have hsub : selected ⊆ words.toFinset := by
      intro u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact hparts i (hvalid.1 hi)
    have hlen : ∀ u ∈ selected, L < u.length := by
      intro u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact hvalid.2.2 i hi
    have hcard : selected.card = J.card := by
      apply Finset.card_image_iff.mpr
      intro i hi j hj heq
      exact ligationCutPart_injective_on isPrefix (hvalid.1 hi) (hvalid.1 hj) heq
    have hsum : L * J.card ≤ selectedWordLengthSum selected words := by
      rw [selectedWordLengthSum_eq_selected_sum selected words hnd hsub]
      calc
        L * J.card = ∑ _u ∈ selected, L := by simp [hcard, Nat.mul_comm]
        _ ≤ ∑ u ∈ selected, u.length := Finset.sum_le_sum (fun u hu => (hlen u hu).le)
    have hcharge : L * w.length ≤ 8 * selectedWordLengthSum selected words := by
      calc
        L * w.length ≤ L * (8 * J.card) := Nat.mul_le_mul_left L hvalid.2.1.le
        _ = 8 * (L * J.card) := by ring
        _ ≤ _ := Nat.mul_le_mul_left 8 hsum
    have hmass : ligationHistoryEventMass p words known (fun bits =>
        ligationCutCertificate L w isPrefix J (ligationHistoryKnown words bits known)) ≤
        finalLigationFailureMass p selected words known := by
      have heq : finalLigationFailureMass p selected words known =
          ligationHistoryEventMass p words known (fun bits =>
            ∀ u ∈ selected, u ∉ ligationHistoryKnown words bits known ∧
              LigationCutDensity (ligationHistoryKnown words bits known) u) := by
        unfold finalLigationFailureMass ligationHistoryEventMass
        apply Finset.sum_congr rfl
        intro bits _
        congr 1
      rw [heq]
      apply ligationHistoryEventMass_mono hp hp1 words known
      intro bits hb u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact (hb.2.2 i hi).2
    apply hmass.trans
    apply (finalLigationFailureMass_le_exp hp hp1 selected words horder
      (fun u _ hu => hL.trans (hlen u hu).le) known).trans
    apply Real.exp_le_exp.mpr
    have hc : (L : ℝ) * w.length ≤ 8 * (selectedWordLengthSum selected words : ℝ) := by
      exact_mod_cast hcharge
    have := mul_le_mul_of_nonneg_left hc hp
    nlinarith
  · have hfalse : ∀ bits, ¬ ligationCutCertificate L w isPrefix J
        (ligationHistoryKnown words bits known) := by
      intro bits hb
      exact hvalid ⟨hb.1, hb.2.1, fun i hi => (hb.2.2 i hi).1⟩
    simp only [ligationHistoryEventMass, hfalse, ↓reduceIte, Finset.sum_const_zero]
    exact (Real.exp_pos _).le

end PowerLawSmallRAF
