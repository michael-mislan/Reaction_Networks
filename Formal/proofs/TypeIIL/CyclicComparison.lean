import Mathlib
import proofs.TypeIIL.CyclicSign
import proofs.TypeIIL.CyclicProduct

namespace TypeIIL

open Function

/-- A cyclic comparison recurrence with physically dissipative gains has no
nonzero mode.  This is the arbitrary-length replacement for the three-sector
comparison lemma used in the original Type II_3 reduction. -/
theorem cyclic_comparison_eq_zero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (next : ι ≃ ι) (hcycle : IsSingleCycle next)
    (u v Y z : ι → ℝ)
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i) (hY : ∀ i, 0 < Y i)
    (hphysical : ∀ i, v i * Y i < u i * Y (next i))
    (hrec : ∀ i,
      z (next.symm i) = (1 + u i) * z i + v i * z (next i)) :
    ∀ i, z i = 0 := by
  classical
  by_contra hnot
  push Not at hnot
  have hsomePos : ∃ i, 0 < z i := by
    by_contra h
    push Not at h
    obtain ⟨k, hk_mem, hkmin⟩ := Finset.exists_min_image Finset.univ z
      (Finset.univ_nonempty)
    obtain ⟨j, hj⟩ := hnot
    have hjneg : z j < 0 := lt_of_le_of_ne (h j) hj
    have hkneg : z k < 0 := lt_of_le_of_lt
      (hkmin j (Finset.mem_univ j)) hjneg
    have hnextnonpos : z (next k) ≤ 0 := h (next k)
    have hprevge : z k ≤ z (next.symm k) :=
      hkmin _ (Finset.mem_univ _)
    have hr := hrec k
    have hu_pos := hu k
    have hv_pos := hv k
    nlinarith
  obtain ⟨k, hk_mem, hkmax⟩ := Finset.exists_max_image Finset.univ z
    (Finset.univ_nonempty)
  have hkpos : 0 < z k := by
    obtain ⟨j, hj⟩ := hsomePos
    exact lt_of_lt_of_le hj (hkmax j (Finset.mem_univ j))
  have hnextneg : z (next k) < 0 := by
    by_contra h
    have hnextnonneg : 0 ≤ z (next k) := le_of_not_gt h
    have hprevle : z (next.symm k) ≤ z k :=
      hkmax _ (Finset.mem_univ _)
    have hr := hrec k
    have hu_pos := hu k
    have hv_pos := hv k
    nlinarith
  let Alternates : ι → Prop := fun i =>
    (0 < z i ∧ z (next i) < 0) ∨ (z i < 0 ∧ 0 < z (next i))
  have hstart : Alternates k := Or.inl ⟨hkpos, hnextneg⟩
  have hprop : ∀ i, Alternates i → Alternates (next i) := by
    intro i hi
    rcases hi with hi | hi
    · have hr := hrec (next i)
      have hv_pos := hv (next i)
      have hnn : 0 < z (next (next i)) := by
        by_contra h
        have hnonpos : z (next (next i)) ≤ 0 := le_of_not_gt h
        have hcoef : 0 < 1 + u (next i) := by linarith [hu (next i)]
        have hfirst : (1 + u (next i)) * z (next i) < 0 :=
          mul_neg_of_pos_of_neg hcoef hi.2
        have hsecond : v (next i) * z (next (next i)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hv_pos) hnonpos
        rw [next.symm_apply_apply] at hr
        linarith
      exact Or.inr ⟨hi.2, hnn⟩
    · have hr := hrec (next i)
      have hv_pos := hv (next i)
      have hnn : z (next (next i)) < 0 := by
        by_contra h
        have hnonneg : 0 ≤ z (next (next i)) := le_of_not_gt h
        have hcoef : 0 < 1 + u (next i) := by linarith [hu (next i)]
        have hfirst : 0 < (1 + u (next i)) * z (next i) :=
          mul_pos hcoef hi.2
        have hsecond : 0 ≤ v (next i) * z (next (next i)) :=
          mul_nonneg (le_of_lt hv_pos) hnonneg
        rw [next.symm_apply_apply] at hr
        linarith
      exact Or.inl ⟨hi.2, hnn⟩
  have horbit : ∀ n : ℕ, Alternates ((next^[n]) k) := by
    intro n
    induction n with
    | zero => simpa using hstart
    | succ n ih =>
        rw [iterate_succ_apply']
        exact hprop _ ih
  have hall : ∀ i, Alternates i := by
    intro i
    rcases hcycle k i with ⟨n, hn⟩
    simpa [hn] using horbit n
  have hz_ne : ∀ i, z i ≠ 0 := by
    intro i
    rcases hall i with hi | hi
    · exact ne_of_gt hi.1
    · exact ne_of_lt hi.1
  have hgrow : ∀ i,
      Y i * |z i| < Y (next i) * |z (next i)| := by
    intro i
    have hr := hrec i
    have hp := hphysical i
    have hv_pos := hv i
    have hYn := hY (next i)
    rcases hall i with hi | hi
    · rw [abs_of_pos hi.1, abs_of_neg hi.2]
      have hprevneg : z (next.symm i) < 0 := by
        have ha := hall (next.symm i)
        rcases ha with ha | ha
        · exact False.elim ((not_lt_of_ge (le_of_lt hi.1))
            (by simpa using ha.2))
        · exact ha.1
      nlinarith
    · rw [abs_of_neg hi.1, abs_of_pos hi.2]
      have hprevpos : 0 < z (next.symm i) := by
        have ha := hall (next.symm i)
        rcases ha with ha | ha
        · exact ha.1
        · exact False.elim ((not_lt_of_ge (le_of_lt hi.1))
            (by simpa using ha.2))
      nlinarith
  have hone : ∀ _ : ι, (1 : ℝ) ≤ 1 := fun _ => le_rfl
  exact impossible_cyclic_growth next (fun _ => 1) Y z hone hY hz_ne
    (by simpa using hgrow)

end TypeIIL
