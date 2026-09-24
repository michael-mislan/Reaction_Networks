import proofs.RAF1519.Refinement.CountLocality

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators

def localCompensator (r d V : ℝ) (N : Fin 7 → ℕ) (a : LocalChannel) (s : Fin 7) : ℝ :=
  (localReaction r d a).rate V N*
    (((localReaction r d a).next N s:ℝ)-(N s:ℝ))/V

theorem local_compensator_stoichiometry (r d V : ℝ) (N : Fin 7 → ℕ)
    (a : LocalChannel) (s : Fin 7) :
    localCompensator r d V N a s = (localReaction r d a).rate V N*
      (((localReaction r d a).produce s:ℝ)-((localReaction r d a).consume s:ℝ))/V := by
  unfold localCompensator
  rw [Reaction.rate_increment]

theorem forward_compensator (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) (j s : Fin 7) :
    localCompensator r d V N (.inl (j,false)) s =
      forwardRate r d (1/100) (1/100) (concentration V N) j*jumps j s := by
  rw [local_compensator_stoichiometry,local_forward_binding r d V hV]
  change V*forwardRate r d (1/100) (1/100) (concentration V N) j*
    ((chemicalOutput j s:ℝ)-(chemicalInput j s:ℝ))/V = _
  rw [chemical_input_output]
  field_simp

theorem reverse_compensator (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) (j s : Fin 7) :
    localCompensator r d V N (.inl (j,true)) s =
      -reverseRate r d (1/100) (1/100) V (concentration V N) j*jumps j s := by
  rw [local_compensator_stoichiometry,local_reverse_binding r d V hV]
  have he : (chemicalInput j s:ℝ)-(chemicalOutput j s:ℝ) = -jumps j s := by
    linarith [chemical_input_output j s]
  change V*reverseRate r d (1/100) (1/100) V (concentration V N) j*
    ((chemicalInput j s:ℝ)-(chemicalOutput j s:ℝ))/V = _
  rw [he]
  field_simp

theorem chemical_compensator_sum (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) (s : Fin 7) :
    (∑ a : Fin 7 × Bool, localCompensator r d V N (.inl a) s) =
      ∑ j : Fin 7, (forwardRate r d (1/100) (1/100) (concentration V N) j-
        reverseRate r d (1/100) (1/100) V (concentration V N) j)*jumps j s := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_bool,reverse_compensator r d V hV,forward_compensator r d V hV]
  ring

theorem food_compensator_sum (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) (s : Fin 7) :
    (∑ a : Fin 2, localCompensator r d V N (.inr (.inl a)) s) =
      ![1,1,0,0,0,0,0] s := by
  simp_rw [local_compensator_stoichiometry,local_food_rate]
  rw [Fin.sum_univ_two]
  simp only [localReaction,Pi.zero_apply,Nat.cast_zero,sub_zero]
  field_simp
  fin_cases s <;> norm_num [Pi.single_apply]
  apply Fin.ext
  norm_num

theorem wash_compensator_sum (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) (s : Fin 7) :
    (∑ a : Fin 7, localCompensator r d V N (.inr (.inr a)) s) =
      -concentration V N s := by
  simp_rw [local_compensator_stoichiometry,local_wash_rate r d V hV]
  simp [localReaction,Pi.single_apply,concentration,← Finset.sum_div]
  ring

theorem local_compensator_sum (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) (s : Fin 7) :
    (∑ a : LocalChannel, localCompensator r d V N a s) =
      countDrift r d (1/100) (1/100) V (concentration V N) s := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type,chemical_compensator_sum r d V hV,
    food_compensator_sum r d V hV,wash_compensator_sum r d V hV]
  unfold countDrift
  ring

end
end RAF1519.Refinement
