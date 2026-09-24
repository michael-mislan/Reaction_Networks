import proofs.PowerLawSmallRAF.LigationHistoryLaw
import proofs.PowerLawSmallRAF.LigationDensityCertificate

namespace PowerLawSmallRAF

def ligationHistoryKnown : (words : List LigationWord) →
    (Fin words.length → Bool) → Finset LigationWord → Finset LigationWord
  | [], _, known => known
  | w :: rest, bits, known =>
      ligationHistoryKnown rest (Fin.tail bits) (if bits 0 then insert w known else known)

theorem subset_ligationHistoryKnown (words : List LigationWord)
    (bits : Fin words.length → Bool) (known : Finset LigationWord) :
    known ⊆ ligationHistoryKnown words bits known := by
  induction words generalizing known with
  | nil => exact Finset.Subset.refl _
  | cons w rest ih =>
      simp only [ligationHistoryKnown]
      split
      · exact (Finset.subset_insert _ _).trans (ih _ _)
      · exact ih _ _

/-- Later steps cannot alter the status of a strictly shorter word. -/
theorem short_mem_ligationHistoryKnown_iff (words : List LigationWord)
    (bits : Fin words.length → Bool) (known : Finset LigationWord)
    (u : LigationWord) (hshort : ∀ w ∈ words, u.length < w.length) :
    u ∈ ligationHistoryKnown words bits known ↔ u ∈ known := by
  induction words generalizing known with
  | nil => rfl
  | cons w rest ih =>
      have hne : u ≠ w := by
        intro h
        have := hshort w (by simp)
        subst u
        omega
      have hr : ∀ v ∈ rest, u.length < v.length := by
        intro v hv
        exact hshort v (List.mem_cons_of_mem _ hv)
      simp only [ligationHistoryKnown]
      rw [ih (Fin.tail bits) _ hr]
      split <;> simp [hne]

theorem density_ligationHistoryKnown_iff (words : List LigationWord)
    (bits : Fin words.length → Bool) (known : Finset LigationWord)
    (u : LigationWord) (hshort : ∀ w ∈ words, u.length ≤ w.length) :
    LigationCutDensity (ligationHistoryKnown words bits known) u ↔
      LigationCutDensity known u := by
  have hmem : ∀ i ∈ ligationCuts u, ∀ isPrefix : Bool,
      ligationCutPart isPrefix u i ∈ ligationHistoryKnown words bits known ↔
        ligationCutPart isPrefix u i ∈ known := by
    intro i hi isPrefix
    apply short_mem_ligationHistoryKnown_iff
    intro w hw
    exact (ligationCutPart_length_lt hi isPrefix).trans_le (hshort w hw)
  have hp : missingPrefixCuts (ligationHistoryKnown words bits known) u =
      missingPrefixCuts known u := by
    ext i
    by_cases hi : i ∈ ligationCuts u
    · simp only [missingPrefixCuts, Finset.mem_filter, hi, true_and]
      exact not_congr (hmem i hi true)
    · simp [missingPrefixCuts, hi]
  have hs : missingSuffixCuts (ligationHistoryKnown words bits known) u =
      missingSuffixCuts known u := by
    ext i
    by_cases hi : i ∈ ligationCuts u
    · simp only [missingSuffixCuts, Finset.mem_filter, hi, true_and]
      exact not_congr (hmem i hi false)
    · simp [missingSuffixCuts, hi]
  simp only [LigationCutDensity, hp, hs]

/-- In length order, final missing words with good final cut density were
already density-qualified failures at their own generation steps. -/
theorem final_density_failures_imply_stopped_history
    (selected : Finset LigationWord) (words : List LigationWord)
    (horder : words.Pairwise (fun u v => u.length ≤ v.length))
    (bits : Fin words.length → Bool) (known : Finset LigationWord)
    (hfinal : ∀ w ∈ words, w ∈ selected →
      w ∉ ligationHistoryKnown words bits known ∧
        LigationCutDensity (ligationHistoryKnown words bits known) w) :
    stoppedLigationHistory selected words bits known := by
  induction words generalizing known with
  | nil => trivial
  | cons w rest ih =>
      obtain ⟨hwrest, hrorder⟩ := List.pairwise_cons.mp horder
      have htail : ∀ v ∈ rest, v ∈ selected →
          v ∉ ligationHistoryKnown rest (Fin.tail bits)
              (if bits 0 then insert w known else known) ∧
            LigationCutDensity (ligationHistoryKnown rest (Fin.tail bits)
              (if bits 0 then insert w known else known)) v := by
        intro v hv hs
        exact hfinal v (List.mem_cons_of_mem _ hv) hs
      have hrec := ih hrorder (Fin.tail bits)
        (if bits 0 then insert w known else known) htail
      by_cases hs : w ∈ selected
      · have hw := hfinal w (by simp) hs
        have hfalse : bits 0 = false := by
          cases hb : bits 0
          · rfl
          · apply False.elim
            apply hw.1
            simp only [ligationHistoryKnown, hb, ↓reduceIte]
            exact subset_ligationHistoryKnown rest (Fin.tail bits) (insert w known)
              (Finset.mem_insert_self _ _)
        have hd : LigationCutDensity known w := by
          apply (density_ligationHistoryKnown_iff (w :: rest) bits known w ?_).mp hw.2
          intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact le_rfl
          · exact hwrest v hv
        simpa [stoppedLigationHistory, hs, hfalse] using And.intro hd (And.intro hfalse hrec)
      · simpa [stoppedLigationHistory, hs] using hrec

noncomputable def finalLigationFailureMass (p : ℝ) (selected : Finset LigationWord)
    (words : List LigationWord) (known : Finset LigationWord) : ℝ := by
  classical
  exact ∑ bits : Fin words.length → Bool,
    if ∀ w ∈ selected, w ∉ ligationHistoryKnown words bits known ∧
        LigationCutDensity (ligationHistoryKnown words bits known) w then
      ligationHistoryWeight p words bits known else 0

/-- A final-state event, rather than a conditional-law assumption, inherits
the stopped exponential bound under the ordered generation law. -/
theorem finalLigationFailureMass_le_exp {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (selected : Finset LigationWord) (words : List LigationWord)
    (horder : words.Pairwise (fun u v => u.length ≤ v.length))
    (hlen : ∀ w ∈ words, w ∈ selected → 4 ≤ w.length)
    (known : Finset LigationWord) :
    finalLigationFailureMass p selected words known ≤
      Real.exp (-p * (selectedWordLengthSum selected words : ℝ) / 2) := by
  classical
  apply le_trans _ (stoppedLigationHistory_mass_le_exp hp hp1 selected words hlen known)
  unfold finalLigationFailureMass
  apply Finset.sum_le_sum
  intro bits _
  unfold stoppedLigationHistoryWeight
  split_ifs with hf hs hs
  · exact le_rfl
  · exact False.elim (hs (final_density_failures_imply_stopped_history selected words
      horder bits known (fun w _ hw => hf w hw)))
  · exact ligationHistoryWeight_nonneg hp hp1 words bits known
  · exact le_rfl

theorem selectedWordLengthSum_eq_finset_sum (selected : Finset LigationWord)
    (words : List LigationWord) (hnd : words.Nodup) :
    selectedWordLengthSum selected words =
      ∑ w ∈ words.toFinset, if w ∈ selected then w.length else 0 := by
  induction words with
  | nil => simp [selectedWordLengthSum]
  | cons w rest ih =>
      obtain ⟨hw, hr⟩ := List.nodup_cons.mp hnd
      rw [List.toFinset_cons, Finset.sum_insert (by simpa using hw)]
      simp only [selectedWordLengthSum, ih hr]

theorem selectedWordLengthSum_eq_selected_sum (selected : Finset LigationWord)
    (words : List LigationWord) (hnd : words.Nodup)
    (hsub : selected ⊆ words.toFinset) :
    selectedWordLengthSum selected words = ∑ w ∈ selected, w.length := by
  rw [selectedWordLengthSum_eq_finset_sum selected words hnd]
  rw [← Finset.sum_subset hsub]
  · simp
  · intro w _ hw
    simp [hw]

end PowerLawSmallRAF
