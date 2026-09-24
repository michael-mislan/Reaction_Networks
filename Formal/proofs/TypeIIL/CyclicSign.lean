import Mathlib
import proofs.TypeIIL.CyclicProduct

namespace TypeIIL

open Function

def IsSingleCycle {ι : Type*} (next : ι ≃ ι) : Prop :=
  ∀ i j, ∃ n : ℕ, (next^[n]) i = j

def Straddles (next : ι ≃ ι) (y : ι → ℝ) (i : ι) : Prop :=
  (1 < y i ∧ y (next i) < 1) ∨ (y i < 1 ∧ 1 < y (next i))

/-- The abstract sign/product engine behind strict Type II_l unistationarity.
The local ratio equation says `delta i` has the opposite sign to
`y(next i)-1`; the species balance is the displayed three-term recurrence. -/
theorem cyclic_sign_product_contradiction
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (next : ι ≃ ι) (hcycle : IsSingleCycle next)
    (m a c d y delta : ι → ℝ)
    (hm : ∀ i, 1 ≤ m i) (ha : ∀ i, 0 < a i)
    (hc : ∀ i, 0 < c i) (hd : ∀ i, 0 < d i)
    (hdc : ∀ i, d i < c i)
    (hneg : ∀ i, delta i < 0 ↔ 1 < y (next i))
    (hpos : ∀ i, 0 < delta i ↔ y (next i) < 1)
    (hbal : ∀ i,
      m i * (a i * (y i - y (next i)) + c i * delta i) +
        d (next i) * delta (next i) = 0)
    (hnonunit : ∃ i, y i ≠ 1) : False := by
  classical
  have hsomeHigh : ∃ i, 1 < y i := by
    by_contra h
    push Not at h
    obtain ⟨k, hk_mem, hkmin⟩ := Finset.exists_min_image Finset.univ y
      (Finset.univ_nonempty)
    rcases hnonunit with ⟨j, hj⟩
    have hjlow : y j < 1 := lt_of_le_of_ne (h j) hj
    have hklow : y k < 1 := lt_of_le_of_lt (hkmin j (Finset.mem_univ j)) hjlow
    let p := next.symm k
    have hdkpos : 0 < delta p := (hpos p).2 (by simpa [p] using hklow)
    have hfirst : 0 < a p * (y p - y k) + c p * delta p := by
      have hy : y p - y k ≥ 0 :=
        sub_nonneg.mpr (hkmin _ (Finset.mem_univ _))
      have hleft : 0 ≤ a p * (y p - y k) :=
        mul_nonneg (le_of_lt (ha p)) hy
      have hright : 0 < c p * delta p := mul_pos (hc p) hdkpos
      linarith
    have hb := hbal p
    have hdeltaKneg : delta k < 0 := by
      rw [show next p = k by simp [p]] at hb
      have hmpos : 0 < m p := lt_of_lt_of_le zero_lt_one (hm p)
      have hprod : d k * delta k < 0 := by
        have : 0 < m p * (a p * (y p - y k) + c p * delta p) :=
          mul_pos hmpos hfirst
        linarith
      rcases (mul_neg_iff.mp hprod) with h | h
      · exact h.2
      · exact False.elim ((not_lt_of_ge (le_of_lt (hd k))) h.1)
    have hnextHigh : 1 < y (next k) := (hneg k).1 hdeltaKneg
    exact (not_lt_of_ge (h (next k))) hnextHigh
  obtain ⟨k, hk_mem, hkmax⟩ := Finset.exists_max_image Finset.univ y
    (Finset.univ_nonempty)
  have hkhigh : 1 < y k := by
    rcases hsomeHigh with ⟨j, hj⟩
    exact lt_of_lt_of_le hj (hkmax j (Finset.mem_univ j))
  let p := next.symm k
  have hp_le : y p ≤ y k := hkmax p (Finset.mem_univ p)
  have hp_delta_neg : delta p < 0 := (hneg p).2 (by simpa [p] using hkhigh)
  have hk_delta_pos : 0 < delta k := by
    have hb := hbal p
    have hsumneg : a p * (y p - y (next p)) + c p * delta p < 0 := by
      have hfirst : a p * (y p - y (next p)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt (ha p))
          (sub_nonpos.mpr (by simpa [p] using hp_le))
      have hsecond : c p * delta p < 0 := mul_neg_of_pos_of_neg (hc p) hp_delta_neg
      linarith
    rw [show next p = k by simp [p]] at hsumneg
    rw [show next p = k by simp [p]] at hb
    have hmpos : 0 < m p := lt_of_lt_of_le zero_lt_one (hm p)
    have hprod : 0 < d k * delta k := by
      have : m p * (a p * (y p - y k) + c p * delta p) < 0 :=
        mul_neg_of_pos_of_neg hmpos hsumneg
      linarith
    rcases (mul_pos_iff.mp hprod) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge (le_of_lt (hd k))) h.1)
  have hknextlow : y (next k) < 1 := (hpos k).1 hk_delta_pos
  have hkstraddle : Straddles next y k := Or.inl ⟨hkhigh, hknextlow⟩
  have hprop : ∀ i, Straddles next y i → Straddles next y (next i) := by
    intro i hi
    rcases hi with hi | hi
    · have hdi : 0 < delta i := (hpos i).2 hi.2
      have hdn : delta (next i) < 0 := by
        have hb := hbal i
        have hdiff : 0 < y i - y (next i) := sub_pos.mpr (lt_trans hi.2 hi.1)
        have hsum : 0 < a i * (y i - y (next i)) + c i * delta i :=
          add_pos (mul_pos (ha i) hdiff) (mul_pos (hc i) hdi)
        have hmpos : 0 < m i := lt_of_lt_of_le zero_lt_one (hm i)
        have hprod : d (next i) * delta (next i) < 0 := by
          have : 0 < m i *
              (a i * (y i - y (next i)) + c i * delta i) := mul_pos hmpos hsum
          linarith
        rcases (mul_neg_iff.mp hprod) with h | h
        · exact h.2
        · exact False.elim ((not_lt_of_ge (le_of_lt (hd (next i)))) h.1)
      exact Or.inr ⟨hi.2, (hneg (next i)).1 hdn⟩
    · have hdi : delta i < 0 := (hneg i).2 hi.2
      have hdn : 0 < delta (next i) := by
        have hb := hbal i
        have hdiff : y i - y (next i) < 0 := sub_neg.mpr (lt_trans hi.1 hi.2)
        have hsum : a i * (y i - y (next i)) + c i * delta i < 0 :=
          add_neg (mul_neg_of_pos_of_neg (ha i) hdiff)
            (mul_neg_of_pos_of_neg (hc i) hdi)
        have hmpos : 0 < m i := lt_of_lt_of_le zero_lt_one (hm i)
        have hprod : 0 < d (next i) * delta (next i) := by
          have : m i *
              (a i * (y i - y (next i)) + c i * delta i) < 0 :=
            mul_neg_of_pos_of_neg hmpos hsum
          linarith
        rcases (mul_pos_iff.mp hprod) with h | h
        · exact h.2
        · exact False.elim ((not_lt_of_ge (le_of_lt (hd (next i)))) h.1)
      exact Or.inl ⟨hi.2, (hpos (next i)).1 hdn⟩
  have horbit : ∀ n : ℕ, Straddles next y ((next^[n]) k) := by
    intro n
    induction n with
    | zero => simpa using hkstraddle
    | succ n ih =>
        rw [iterate_succ_apply']
        exact hprop _ ih
  have hall : ∀ i, Straddles next y i := by
    intro i
    rcases hcycle k i with ⟨n, hn⟩
    simpa [hn] using horbit n
  have hdelta_ne : ∀ i, delta i ≠ 0 := by
    intro i
    rcases hall i with hi | hi
    · exact ne_of_gt ((hpos i).2 hi.2)
    · exact ne_of_lt ((hneg i).2 hi.2)
  have hgrow : ∀ i,
      m i * (d i * |delta i|) < d (next i) * |delta (next i)| := by
    intro i
    rcases hall i with hi | hi
    · have hdi : 0 < delta i := (hpos i).2 hi.2
      have hn := hprop i (Or.inl hi)
      rcases hn with hn | hn
      · exact False.elim ((not_lt_of_ge (le_of_lt hi.2)) hn.1)
      have hdn : delta (next i) < 0 := (hneg (next i)).2 hn.2
      rw [abs_of_pos hdi, abs_of_neg hdn]
      have hb := hbal i
      have hdiff : 0 < y i - y (next i) := sub_pos.mpr (lt_trans hi.2 hi.1)
      have hmpos : 0 < m i := lt_of_lt_of_le zero_lt_one (hm i)
      have hadiff : 0 < a i * (y i - y (next i)) := mul_pos (ha i) hdiff
      have hdcDelta : d i * delta i < c i * delta i :=
        mul_lt_mul_of_pos_right (hdc i) hdi
      have hinner : d i * delta i <
          a i * (y i - y (next i)) + c i * delta i := by linarith
      have hscaled := mul_lt_mul_of_pos_left hinner hmpos
      linarith
    · have hdi : delta i < 0 := (hneg i).2 hi.2
      have hn := hprop i (Or.inr hi)
      rcases hn with hn | hn
      · have hdn : 0 < delta (next i) := (hpos (next i)).2 hn.2
        rw [abs_of_neg hdi, abs_of_pos hdn]
        have hb := hbal i
        have hdiff : y i - y (next i) < 0 := sub_neg.mpr (lt_trans hi.1 hi.2)
        have hmpos : 0 < m i := lt_of_lt_of_le zero_lt_one (hm i)
        have hnegDelta : 0 < -delta i := neg_pos.mpr hdi
        have hadiff : a i * (y i - y (next i)) < 0 :=
          mul_neg_of_pos_of_neg (ha i) hdiff
        have hdcDelta : d i * (-delta i) < c i * (-delta i) :=
          mul_lt_mul_of_pos_right (hdc i) hnegDelta
        have hinner : d i * (-delta i) <
            -(a i * (y i - y (next i)) + c i * delta i) := by linarith
        have hscaled := mul_lt_mul_of_pos_left hinner hmpos
        linarith
      · exact False.elim ((not_lt_of_ge (le_of_lt hi.2)) hn.1)
  exact impossible_cyclic_growth next m d delta hm hd hdelta_ne hgrow

end TypeIIL
