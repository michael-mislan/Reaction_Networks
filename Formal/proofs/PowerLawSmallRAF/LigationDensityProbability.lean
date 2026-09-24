import proofs.PowerLawSmallRAF.LigationWitnessProbability

namespace PowerLawSmallRAF

open scoped BigOperators

theorem ligationCutCertificate_union_mass_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (words : List LigationWord) (hnd : words.Nodup)
    (horder : words.Pairwise (fun u v => u.length ≤ v.length))
    (known : Finset LigationWord) (L : Nat) (hL : 4 ≤ L)
    (hlarge : 32 * Real.log 2 ≤ p * (L : ℝ))
    (w : LigationWord) (isPrefix : Bool)
    (hparts : ∀ i ∈ ligationCuts w, ligationCutPart isPrefix w i ∈ words.toFinset) :
    ligationHistoryEventMass p words known (fun bits =>
      ∃ J ∈ (ligationCuts w).powerset,
        ligationCutCertificate L w isPrefix J (ligationHistoryKnown words bits known)) ≤
      Real.exp (-p * (L : ℝ)^2 / 32) := by
  classical
  by_cases hLw : L ≤ w.length
  · apply (ligationHistoryEventMass_union_le hp hp1 words known _ _).trans
    have hsum : (∑ J ∈ (ligationCuts w).powerset,
        ligationHistoryEventMass p words known (fun bits =>
          ligationCutCertificate L w isPrefix J (ligationHistoryKnown words bits known))) ≤
        (2 : ℝ)^w.length * Real.exp (-p * (L : ℝ) * (w.length : ℝ) / 16) := by
      calc
        _ ≤ ∑ _J ∈ (ligationCuts w).powerset,
            Real.exp (-p * (L : ℝ) * (w.length : ℝ) / 16) := by
          apply Finset.sum_le_sum
          intro J _
          exact ligationCutCertificate_mass_le hp hp1 words hnd horder known L hL w isPrefix J hparts
        _ = (2 : ℝ)^(ligationCuts w).card *
            Real.exp (-p * (L : ℝ) * (w.length : ℝ) / 16) := by
          simp [Finset.card_powerset]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          have hs : ligationCuts w ⊆ Finset.range w.length := by
            intro i hi
            exact Finset.mem_range.mpr (Finset.mem_Ioo.mp hi).2
          simpa using Finset.card_le_card hs
    exact hsum.trans (ligation_density_entropy_bound hp L w.length hLw hlarge)
  · have hfalse : ∀ bits, ¬ ∃ J ∈ (ligationCuts w).powerset,
        ligationCutCertificate L w isPrefix J (ligationHistoryKnown words bits known) := by
      intro bits ⟨J, _, hb⟩
      have hn : J.Nonempty := by
        apply Finset.card_pos.mp
        have := hb.2.1
        omega
      obtain ⟨i, hi⟩ := hn
      have hlong := (hb.2.2 i hi).1
      have hshort := ligationCutPart_length_lt (hb.1 hi) isPrefix
      omega
    simp only [ligationHistoryEventMass, hfalse, ↓reduceIte, Finset.sum_const_zero]
    exact (Real.exp_pos _).le

/-- All final density failures are bounded by a finite witness union. This
theorem has no assumed per-witness probability estimate. -/
theorem ligationDensityFailure_mass_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (words : List LigationWord) (hnd : words.Nodup)
    (horder : words.Pairwise (fun u v => u.length ≤ v.length))
    (ambient known : Finset LigationWord) (L : Nat) (hL : 4 ≤ L)
    (hlarge : 32 * Real.log 2 ≤ p * (L : ℝ))
    (hclosed : ∀ w ∈ ambient, ∀ i ∈ ligationCuts w, ∀ isPrefix : Bool,
      ligationCutPart isPrefix w i ∈ ambient)
    (hfood : ∀ w ∈ ambient, w.length ≤ L → w ∈ known)
    (hcover : ambient ⊆ words.toFinset) :
    ligationHistoryEventMass p words known (fun bits =>
      ∃ w ∈ ambient, ¬ LigationCutDensity (ligationHistoryKnown words bits known) w) ≤
      2 * (ambient.card : ℝ) * Real.exp (-p * (L : ℝ)^2 / 32) := by
  classical
  let event := fun (w : LigationWord) (isPrefix : Bool) (bits : Fin words.length → Bool) =>
    ∃ J ∈ (ligationCuts w).powerset,
      ligationCutCertificate L w isPrefix J (ligationHistoryKnown words bits known)
  have hcoverEvent : ∀ bits,
      (∃ w ∈ ambient, ¬ LigationCutDensity (ligationHistoryKnown words bits known) w) →
      ∃ w ∈ ambient, ∃ isPrefix ∈ (Finset.univ : Finset Bool), event w isPrefix bits := by
    intro bits hb
    obtain ⟨w, hw, isPrefix, J, hJ, hcard, hparts⟩ :=
      exists_first_ligation_density_certificate ambient (ligationHistoryKnown words bits known)
        L hclosed (fun u hu hlen => subset_ligationHistoryKnown words bits known (hfood u hu hlen)) hb
    exact ⟨w, hw, isPrefix, Finset.mem_univ _, J, Finset.mem_powerset.mpr hJ, hJ, hcard, hparts⟩
  apply (ligationHistoryEventMass_mono hp hp1 words known _ _ hcoverEvent).trans
  apply (ligationHistoryEventMass_union_le hp hp1 words known ambient _).trans
  calc
    _ ≤ ∑ w ∈ ambient, ∑ isPrefix : Bool,
        ligationHistoryEventMass p words known (event w isPrefix) := by
      apply Finset.sum_le_sum
      intro w _
      exact ligationHistoryEventMass_union_le hp hp1 words known Finset.univ (event w)
    _ ≤ ∑ _w ∈ ambient, ∑ _isPrefix : Bool, Real.exp (-p * (L : ℝ)^2 / 32) := by
      apply Finset.sum_le_sum
      intro w hw
      apply Finset.sum_le_sum
      intro isPrefix _
      exact ligationCutCertificate_union_mass_le hp hp1 words hnd horder known L hL hlarge
        w isPrefix (fun i hi => hcover (hclosed w hw i hi isPrefix))
    _ = _ := by simp; ring

theorem ligationHistoryEventMass_or_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (words : List LigationWord) (known : Finset LigationWord) (P Q) :
    ligationHistoryEventMass p words known (fun bits => P bits ∨ Q bits) ≤
      ligationHistoryEventMass p words known P + ligationHistoryEventMass p words known Q := by
  classical
  unfold ligationHistoryEventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro bits _
  have hn := ligationHistoryWeight_nonneg hp hp1 words bits known
  by_cases hP : P bits <;> by_cases hQ : Q bits <;> simp [hP, hQ]
  linarith

/-- Finite target bound under the explicit ordered history law. The ambient
set may be the distinct nonempty substrings of the target. -/
theorem ligationTarget_history_mass_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (words : List LigationWord) (hnd : words.Nodup)
    (horder : words.Pairwise (fun u v => u.length ≤ v.length))
    (ambient known : Finset LigationWord) (L : Nat) (hL : 4 ≤ L)
    (hlarge : 32 * Real.log 2 ≤ p * (L : ℝ))
    (hclosed : ∀ w ∈ ambient, ∀ i ∈ ligationCuts w, ∀ isPrefix : Bool,
      ligationCutPart isPrefix w i ∈ ambient)
    (hfood : ∀ w ∈ ambient, w.length ≤ L → w ∈ known)
    (hcover : ambient ⊆ words.toFinset) (target : LigationWord)
    (htarget : target ∈ ambient) (htlen : L ≤ target.length) :
    ligationHistoryEventMass p words known (fun bits =>
      target ∉ ligationHistoryKnown words bits known) ≤
      Real.exp (-p * (target.length : ℝ) / 2) +
        2 * (ambient.card : ℝ) * Real.exp (-p * (L : ℝ)^2 / 32) := by
  classical
  let P := fun bits : Fin words.length → Bool =>
    target ∉ ligationHistoryKnown words bits known ∧
      LigationCutDensity (ligationHistoryKnown words bits known) target
  let Q := fun bits : Fin words.length → Bool =>
    ∃ w ∈ ambient, ¬ LigationCutDensity (ligationHistoryKnown words bits known) w
  have hsplit : ∀ bits, target ∉ ligationHistoryKnown words bits known → P bits ∨ Q bits := by
    intro bits hm
    by_cases hd : LigationCutDensity (ligationHistoryKnown words bits known) target
    · exact Or.inl ⟨hm, hd⟩
    · exact Or.inr ⟨target, htarget, hd⟩
  have hP : ligationHistoryEventMass p words known P ≤
      Real.exp (-p * (target.length : ℝ) / 2) := by
    have hs : ({target} : Finset LigationWord) ⊆ words.toFinset := by
      simpa using hcover htarget
    have heq : ligationHistoryEventMass p words known P =
        finalLigationFailureMass p {target} words known := by
      simp [ligationHistoryEventMass, finalLigationFailureMass, P]
      apply Finset.sum_congr rfl
      intro bits _
      congr 1
    rw [heq]
    have hbound := finalLigationFailureMass_le_exp hp hp1 {target} words horder
      (fun u _ hu => by
        have heq : u = target := Finset.mem_singleton.mp hu
        simpa only [heq] using hL.trans htlen) known
    rw [selectedWordLengthSum_eq_selected_sum {target} words hnd hs] at hbound
    simpa using hbound
  apply (ligationHistoryEventMass_mono hp hp1 words known _ _ hsplit).trans
  apply (ligationHistoryEventMass_or_le hp hp1 words known P Q).trans
  exact add_le_add hP (ligationDensityFailure_mass_le hp hp1 words hnd horder
    ambient known L hL hlarge hclosed hfood hcover)

end PowerLawSmallRAF
