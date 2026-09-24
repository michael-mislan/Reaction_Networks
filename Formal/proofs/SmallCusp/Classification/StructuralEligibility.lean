import proofs.SmallCusp.Obstruction.FewReactantObstruction

namespace SmallCusp

open scoped BigOperators

def codedCross (C : CodedBimolNetwork) (r s : Fin 5) : ℤ :=
  codedStoich C 0 r * codedStoich C 1 s -
    codedStoich C 0 s * codedStoich C 1 r

/-- The generator columns surround the origin: every nonzero column sees
columns strictly on both sides of its line. -/
def CodedKernelBalanced (C : CodedBimolNetwork) : Prop :=
  ∀ r, (codedStoich C 0 r ≠ 0 ∨ codedStoich C 1 r ≠ 0) →
    (∃ s, codedCross C r s < 0) ∧ (∃ s, 0 < codedCross C r s)

instance codedKernelBalanced_decidable (C : CodedBimolNetwork) :
    Decidable (CodedKernelBalanced C) := by
  unfold CodedKernelBalanced
  infer_instance

private theorem coded_massAction_unit_eq_sum (C : CodedBimolNetwork)
    (v : Fin 5 → ℝ) (i : Species) :
    C.toNetwork.massAction v unitState i =
      ∑ r, (codedStoich C i r : ℝ) * v r := by
  unfold SmallPlanarNetwork.massAction SmallPlanarNetwork.monomial
  apply Finset.sum_congr rfl
  intro r _
  simp [CodedBimolNetwork.toNetwork, SmallPlanarNetwork.stoich,
    codedStoich, unitState]

private theorem codedCross_exists_ne_zero (C : CodedBimolNetwork)
    (hrank : C.toNetwork.HasStoichiometricRankTwo) (r : Fin 5)
    (hr : codedStoich C 0 r ≠ 0 ∨ codedStoich C 1 r ≠ 0) :
    ∃ s, codedCross C r s ≠ 0 := by
  rcases hrank with ⟨a, b, hab⟩
  by_contra h
  push Not at h
  have hra := h a
  have hrb := h b
  change codedCross C a b ≠ 0 at hab
  rcases hr with hr0 | hr1
  · have hid : codedStoich C 0 r * codedCross C a b =
        codedStoich C 0 a * codedCross C r b -
          codedStoich C 0 b * codedCross C r a := by
      unfold codedCross
      ring
    rw [hra, hrb] at hid
    exact (mul_ne_zero hr0 hab) (by simpa using hid)
  · have hid : codedStoich C 1 r * codedCross C a b =
        codedStoich C 1 a * codedCross C r b -
          codedStoich C 1 b * codedCross C r a := by
      unfold codedCross
      ring
    rw [hra, hrb] at hid
    exact (mul_ne_zero hr1 hab) (by simpa using hid)

theorem codedKernelBalanced_of_positive_equilibrium
    (C : CodedBimolNetwork) (v : Fin 5 → ℝ)
    (hrank : C.toNetwork.HasStoichiometricRankTwo)
    (hv : PositiveVector v)
    (heq : ∀ i, C.toNetwork.massAction v unitState i = 0) :
    CodedKernelBalanced C := by
  have heq' : ∀ i, ∑ s, (codedStoich C i s : ℝ) * v s = 0 := by
    intro i
    rw [← coded_massAction_unit_eq_sum]
    exact heq i
  intro r hr
  obtain ⟨t, ht⟩ := codedCross_exists_ne_zero C hrank r hr
  have hsum : ∑ s, v s * (codedCross C r s : ℝ) = 0 := by
    rw [show (∑ s, v s * (codedCross C r s : ℝ)) =
        (codedStoich C 0 r : ℝ) *
            (∑ s, (codedStoich C 1 s : ℝ) * v s) -
          (codedStoich C 1 r : ℝ) *
            (∑ s, (codedStoich C 0 s : ℝ) * v s) by
      simp only [codedCross, Int.cast_sub, Int.cast_mul]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro s _ <;> ring]
    rw [heq' 0, heq' 1]
    ring
  constructor
  · by_contra hn
    push Not at hn
    have hnonneg : ∀ s, 0 ≤ v s * (codedCross C r s : ℝ) := by
      intro s
      exact mul_nonneg (le_of_lt (hv s)) (by exact_mod_cast hn s)
    have htpos : 0 < v t * (codedCross C r t : ℝ) := by
      apply mul_pos (hv t)
      exact_mod_cast (lt_of_le_of_ne (hn t) (Ne.symm ht))
    have : 0 < ∑ s, v s * (codedCross C r s : ℝ) :=
      Finset.sum_pos' (fun s _ ↦ hnonneg s) ⟨t, Finset.mem_univ _, htpos⟩
    linarith
  · by_contra hp
    push Not at hp
    have hnonneg : ∀ s, 0 ≤ v s * (-(codedCross C r s : ℝ)) := by
      intro s
      apply mul_nonneg (le_of_lt (hv s))
      exact neg_nonneg.mpr (by exact_mod_cast hp s)
    have htpos : 0 < v t * (-(codedCross C r t : ℝ)) := by
      apply mul_pos (hv t)
      apply neg_pos.mpr
      exact_mod_cast (lt_of_le_of_ne (hp t) ht)
    have : 0 < ∑ s, v s * (-(codedCross C r s : ℝ)) :=
      Finset.sum_pos' (fun s _ ↦ hnonneg s) ⟨t, Finset.mem_univ _, htpos⟩
    have hneg : (∑ s, v s * (-(codedCross C r s : ℝ))) = 0 := by
      calc
        (∑ s, v s * (-(codedCross C r s : ℝ))) =
            -(∑ s, v s * (codedCross C r s : ℝ)) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro s _
              ring
        _ = 0 := by rw [hsum]; norm_num
    linarith

theorem cusp_implies_codedKernelBalanced (Q : SmallPlanarNetwork 5)
    (hQ : IsPlanarBimolecular252 Q) (hcusp : AdmitsTransverseCusp Q) :
    CodedKernelBalanced (encodeBimolNetwork Q hQ.1 hQ.2.1) := by
  obtain ⟨D, hD⟩ := admitsTransverseCusp_implies_traceFreeNormalized Q hcusp
  have hnet := encodeBimolNetwork_toNetwork Q hQ.1 hQ.2.1
  apply codedKernelBalanced_of_positive_equilibrium
    (encodeBimolNetwork Q hQ.1 hQ.2.1) D.rates
  · simpa [hnet] using hQ.2.2.1
  · exact hD.2.1
  · intro i
    simpa [hnet, hD.1] using hD.2.2.1 i

end SmallCusp
