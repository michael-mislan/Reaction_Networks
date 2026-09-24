import proofs.PowerLawSmallRAF.FiniteLigationExposure

namespace PowerLawSmallRAF

def ligationCutPart (isPrefix : Bool) (w : LigationWord) (i : Nat) : LigationWord :=
  if isPrefix then w.take i else w.drop i

theorem ligationCutPart_length_lt {w : LigationWord} {i : Nat}
    (hi : i ∈ ligationCuts w) (isPrefix : Bool) :
    (ligationCutPart isPrefix w i).length < w.length := by
  have h := Finset.mem_Ioo.mp hi
  cases isPrefix <;> simp only [ligationCutPart, Bool.false_eq_true, ↓reduceIte,
    List.length_drop, List.length_take] <;> omega

theorem ligationCutPart_injective_on {w : LigationWord} (isPrefix : Bool) :
    Set.InjOn (ligationCutPart isPrefix w) (ligationCuts w : Set Nat) := by
  intro i hi j hj heq
  have hi' := Finset.mem_Ioo.mp hi
  have hj' := Finset.mem_Ioo.mp hj
  have hlen := congrArg List.length heq
  cases isPrefix <;> simp only [ligationCutPart, Bool.false_eq_true, ↓reduceIte,
    List.length_drop, List.length_take] at hlen <;> omega

/-- Static first-failure certificate. The ambient word set is finite and
closed under the relevant proper prefixes/suffixes. Every selected failed
word is shorter than the first density failure, and therefore itself has
good cut density. No independence premise is used. -/
theorem exists_first_ligation_density_certificate
    (ambient known : Finset LigationWord) (L : Nat)
    (hclosed : ∀ w ∈ ambient, ∀ i ∈ ligationCuts w, ∀ isPrefix : Bool,
      ligationCutPart isPrefix w i ∈ ambient)
    (hfood : ∀ w ∈ ambient, w.length ≤ L → w ∈ known)
    (hbad : ∃ w ∈ ambient, ¬ LigationCutDensity known w) :
    ∃ w ∈ ambient, ∃ isPrefix : Bool, ∃ J : Finset Nat,
      J ⊆ ligationCuts w ∧ w.length < 8 * J.card ∧
      ∀ i ∈ J,
        L < (ligationCutPart isPrefix w i).length ∧
        ligationCutPart isPrefix w i ∉ known ∧
        LigationCutDensity known (ligationCutPart isPrefix w i) := by
  classical
  let bad := ambient.filter fun w => ¬ LigationCutDensity known w
  have hb : bad.Nonempty := by
    obtain ⟨w, hw, hd⟩ := hbad
    exact ⟨w, Finset.mem_filter.mpr ⟨hw, hd⟩⟩
  let lengths := bad.image List.length
  have hl : lengths.Nonempty := Finset.Nonempty.image hb _
  obtain ⟨w, hwbad, hwlen⟩ := Finset.mem_image.mp (Finset.min'_mem lengths hl)
  have hw : w ∈ ambient := (Finset.mem_filter.mp hwbad).1
  have hwd : ¬ LigationCutDensity known w := (Finset.mem_filter.mp hwbad).2
  have hminimal : ∀ u ∈ ambient, u.length < w.length → LigationCutDensity known u := by
    intro u hu hshort
    by_contra hd
    have huBad : u ∈ bad := Finset.mem_filter.mpr ⟨hu, hd⟩
    have hle := Finset.min'_le lengths u.length (Finset.mem_image.mpr ⟨u, huBad, rfl⟩)
    omega
  have hparts : ∀ (isPrefix : Bool) (J : Finset Nat), J ⊆ ligationCuts w →
      (∀ i ∈ J, ligationCutPart isPrefix w i ∉ known) →
      ∀ i ∈ J,
        L < (ligationCutPart isPrefix w i).length ∧
        ligationCutPart isPrefix w i ∉ known ∧
        LigationCutDensity known (ligationCutPart isPrefix w i) := by
    intro isPrefix J hJ hmiss i hi
    have hmem := hclosed w hw i (hJ hi) isPrefix
    have hnot := hmiss i hi
    refine ⟨?_, hnot, hminimal _ hmem (ligationCutPart_length_lt (hJ hi) isPrefix)⟩
    by_contra hlen
    exact hnot (hfood _ hmem (by omega))
  by_cases hp : 8 * (missingPrefixCuts known w).card ≤ w.length
  · have hs : w.length < 8 * (missingSuffixCuts known w).card := by
      by_contra h
      exact hwd ⟨hp, by omega⟩
    refine ⟨w, hw, false, missingSuffixCuts known w, Finset.filter_subset _ _, hs, ?_⟩
    apply hparts false _ (Finset.filter_subset _ _)
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  · have hp' : w.length < 8 * (missingPrefixCuts known w).card := by omega
    refine ⟨w, hw, true, missingPrefixCuts known w, Finset.filter_subset _ _, hp', ?_⟩
    apply hparts true _ (Finset.filter_subset _ _)
    intro i hi
    exact (Finset.mem_filter.mp hi).2

/-- The subset entropy in a first-density-failure certificate is absorbed by
its stopped length charge. This is the numerical inequality used after the
finite witness union, with the constants of the current target bound. -/
theorem ligation_density_entropy_bound {p : ℝ} (hp : 0 ≤ p)
    (L m : Nat) (hLm : L ≤ m) (hlarge : 32 * Real.log 2 ≤ p * (L : ℝ)) :
    (2 : ℝ) ^ m * Real.exp (-p * (L : ℝ) * (m : ℝ) / 16) ≤
      Real.exp (-p * (L : ℝ) ^ 2 / 32) := by
  have hpow : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlargeM := mul_le_mul_of_nonneg_right hlarge (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hcast : (L : ℝ) ≤ m := by exact_mod_cast hLm
  have hproduct := mul_le_mul_of_nonneg_left hcast
    (mul_nonneg hp (Nat.cast_nonneg L : (0 : ℝ) ≤ L))
  nlinarith

end PowerLawSmallRAF
