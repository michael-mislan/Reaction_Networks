import proofs.RAF1519.Refinement.CountNetwork

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

def concentration (V : ℝ) (N : Fin 7 → ℕ) : State := fun i => (N i:ℝ)/V

theorem prod_seven (f : Fin 7 → ℝ) :
    (∏ i, f i) = f 0*f 1*f 2*f 3*f 4*f 5*f 6 := by
  simp [Fin.prod_univ_succ]
  ring

theorem cast_descFactorial_two (N : ℕ) :
    (N.descFactorial 2:ℝ) = (N:ℝ)*((N:ℝ)-1) := by
  cases N with
  | zero => norm_num [Nat.descFactorial_succ]
  | succ N =>
    simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.sub_zero,
      Nat.add_one_sub_one,mul_one,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    ring

theorem forward_0 (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (localReaction r d (.inl (0,false))).rate V N =
      V*forwardRate r d (1/100) (1/100) (concentration V N) 0 := by
  rw [Reaction.rate,prod_seven]
  change (1/500000000:ℝ)*V*((((N 0).descFactorial 1:ℝ)/V^1)*(((N 1).descFactorial 1:ℝ)/V^1)*(((N 2).descFactorial 0:ℝ)/V^0)*(((N 3).descFactorial 0:ℝ)/V^0)*(((N 4).descFactorial 0:ℝ)/V^0)*(((N 5).descFactorial 0:ℝ)/V^0)*(((N 6).descFactorial 0:ℝ)/V^0)) = V*((1/500000000)*((N 0:ℝ)/V)*((N 1:ℝ)/V))
  norm_num
  field_simp

theorem forward_1 (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (localReaction r d (.inl (1,false))).rate V N =
      V*forwardRate r d (1/100) (1/100) (concentration V N) 1 := by
  rw [Reaction.rate,prod_seven]
  change 20*V*((((N 0).descFactorial 1:ℝ)/V^1)*(((N 1).descFactorial 0:ℝ)/V^0)*(((N 2).descFactorial 1:ℝ)/V^1)*(((N 3).descFactorial 0:ℝ)/V^0)*(((N 4).descFactorial 0:ℝ)/V^0)*(((N 5).descFactorial 0:ℝ)/V^0)*(((N 6).descFactorial 0:ℝ)/V^0)) = V*(20*((N 2:ℝ)/V)*((N 0:ℝ)/V))
  norm_num
  field_simp

theorem forward_2 (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (localReaction r d (.inl (2,false))).rate V N =
      V*forwardRate r d (1/100) (1/100) (concentration V N) 2 := by
  rw [Reaction.rate,prod_seven]
  change 20*V*((((N 0).descFactorial 0:ℝ)/V^0)*(((N 1).descFactorial 1:ℝ)/V^1)*(((N 2).descFactorial 0:ℝ)/V^0)*(((N 3).descFactorial 1:ℝ)/V^1)*(((N 4).descFactorial 0:ℝ)/V^0)*(((N 5).descFactorial 0:ℝ)/V^0)*(((N 6).descFactorial 0:ℝ)/V^0)) = V*(20*((N 3:ℝ)/V)*((N 1:ℝ)/V))
  norm_num
  field_simp

theorem forward_3 (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (localReaction r d (.inl (3,false))).rate V N =
      V*forwardRate r d (1/100) (1/100) (concentration V N) 3 := by
  rw [Reaction.rate,prod_seven]
  change 20*V*((((N 0).descFactorial 0:ℝ)/V^0)*(((N 1).descFactorial 0:ℝ)/V^0)*(((N 2).descFactorial 0:ℝ)/V^0)*(((N 3).descFactorial 0:ℝ)/V^0)*(((N 4).descFactorial 1:ℝ)/V^1)*(((N 5).descFactorial 0:ℝ)/V^0)*(((N 6).descFactorial 0:ℝ)/V^0)) = V*(20*((N 4:ℝ)/V))
  norm_num
  field_simp

theorem forward_4 (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (localReaction r d (.inl (4,false))).rate V N =
      V*forwardRate r d (1/100) (1/100) (concentration V N) 4 := by
  rw [Reaction.rate,prod_seven]
  change r*V*((((N 0).descFactorial 0:ℝ)/V^0)*(((N 1).descFactorial 0:ℝ)/V^0)*(((N 2).descFactorial 0:ℝ)/V^0)*(((N 3).descFactorial 0:ℝ)/V^0)*(((N 4).descFactorial 0:ℝ)/V^0)*(((N 5).descFactorial 1:ℝ)/V^1)*(((N 6).descFactorial 0:ℝ)/V^0)) = V*(r*((N 5:ℝ)/V))
  norm_num
  field_simp

theorem forward_5 (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (localReaction r d (.inl (5,false))).rate V N =
      V*forwardRate r d (1/100) (1/100) (concentration V N) 5 := by
  rw [Reaction.rate,prod_seven]
  change (d*(101/100))*V*((((N 0).descFactorial 0:ℝ)/V^0)*(((N 1).descFactorial 0:ℝ)/V^0)*(((N 2).descFactorial 1:ℝ)/V^1)*(((N 3).descFactorial 0:ℝ)/V^0)*(((N 4).descFactorial 0:ℝ)/V^0)*(((N 5).descFactorial 0:ℝ)/V^0)*(((N 6).descFactorial 0:ℝ)/V^0)) = V*(d*(1+1/100)*((N 2:ℝ)/V))
  norm_num
  field_simp

theorem forward_6 (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (localReaction r d (.inl (6,false))).rate V N =
      V*forwardRate r d (1/100) (1/100) (concentration V N) 6 := by
  rw [Reaction.rate,prod_seven]
  change (100*d)*V*((((N 0).descFactorial 0:ℝ)/V^0)*(((N 1).descFactorial 0:ℝ)/V^0)*(((N 2).descFactorial 0:ℝ)/V^0)*(((N 3).descFactorial 0:ℝ)/V^0)*(((N 4).descFactorial 0:ℝ)/V^0)*(((N 5).descFactorial 0:ℝ)/V^0)*(((N 6).descFactorial 1:ℝ)/V^1)) = V*(d/(1/100)*((N 6:ℝ)/V))
  norm_num
  field_simp

theorem reverse_0 (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (localReaction r d (.inl (0,true))).rate V N =
      V*reverseRate r d (1/100) (1/100) V (concentration V N) 0 := by
  rw [Reaction.rate,prod_seven]
  change (1/5000000000:ℝ)*V*((((N 0).descFactorial 0:ℝ)/V^0)*(((N 1).descFactorial 0:ℝ)/V^0)*(((N 2).descFactorial 1:ℝ)/V^1)*(((N 3).descFactorial 0:ℝ)/V^0)*(((N 4).descFactorial 0:ℝ)/V^0)*(((N 5).descFactorial 0:ℝ)/V^0)*(((N 6).descFactorial 0:ℝ)/V^0)) = V*((1/5000000000)*((N 2:ℝ)/V))
  norm_num
  field_simp

theorem reverse_1 (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (localReaction r d (.inl (1,true))).rate V N =
      V*reverseRate r d (1/100) (1/100) V (concentration V N) 1 := by
  rw [Reaction.rate,prod_seven]
  change 20*V*((((N 0).descFactorial 0:ℝ)/V^0)*(((N 1).descFactorial 0:ℝ)/V^0)*(((N 2).descFactorial 0:ℝ)/V^0)*(((N 3).descFactorial 1:ℝ)/V^1)*(((N 4).descFactorial 0:ℝ)/V^0)*(((N 5).descFactorial 0:ℝ)/V^0)*(((N 6).descFactorial 0:ℝ)/V^0)) = V*(20*((N 3:ℝ)/V))
  norm_num
  field_simp

theorem reverse_2 (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (localReaction r d (.inl (2,true))).rate V N =
      V*reverseRate r d (1/100) (1/100) V (concentration V N) 2 := by
  rw [Reaction.rate,prod_seven]
  change 20*V*((((N 0).descFactorial 0:ℝ)/V^0)*(((N 1).descFactorial 0:ℝ)/V^0)*(((N 2).descFactorial 0:ℝ)/V^0)*(((N 3).descFactorial 0:ℝ)/V^0)*(((N 4).descFactorial 1:ℝ)/V^1)*(((N 5).descFactorial 0:ℝ)/V^0)*(((N 6).descFactorial 0:ℝ)/V^0)) = V*(20*((N 4:ℝ)/V))
  norm_num
  field_simp

theorem reverse_3 (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (localReaction r d (.inl (3,true))).rate V N =
      V*reverseRate r d (1/100) (1/100) V (concentration V N) 3 := by
  rw [Reaction.rate,prod_seven]
  change 2*V*((((N 0).descFactorial 0:ℝ)/V^0)*(((N 1).descFactorial 0:ℝ)/V^0)*(((N 2).descFactorial 0:ℝ)/V^0)*(((N 3).descFactorial 0:ℝ)/V^0)*(((N 4).descFactorial 0:ℝ)/V^0)*(((N 5).descFactorial 1:ℝ)/V^1)*(((N 6).descFactorial 0:ℝ)/V^0)) = V*(2*((N 5:ℝ)/V))
  norm_num
  field_simp

theorem reverse_4 (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (localReaction r d (.inl (4,true))).rate V N =
      V*reverseRate r d (1/100) (1/100) V (concentration V N) 4 := by
  rw [Reaction.rate,prod_seven]
  change r*V*((((N 0).descFactorial 0:ℝ)/V^0)*(((N 1).descFactorial 0:ℝ)/V^0)*(((N 2).descFactorial 2:ℝ)/V^2)*(((N 3).descFactorial 0:ℝ)/V^0)*(((N 4).descFactorial 0:ℝ)/V^0)*(((N 5).descFactorial 0:ℝ)/V^0)*(((N 6).descFactorial 0:ℝ)/V^0)) = V*(r*(((N 2:ℝ)/V)^2-((N 2:ℝ)/V)/V))
  simp only [cast_descFactorial_two]
  norm_num
  field_simp

theorem reverse_5 (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (localReaction r d (.inl (5,true))).rate V N =
      V*reverseRate r d (1/100) (1/100) V (concentration V N) 5 := by
  rw [Reaction.rate,prod_seven]
  change d*V*((((N 0).descFactorial 0:ℝ)/V^0)*(((N 1).descFactorial 0:ℝ)/V^0)*(((N 2).descFactorial 0:ℝ)/V^0)*(((N 3).descFactorial 0:ℝ)/V^0)*(((N 4).descFactorial 0:ℝ)/V^0)*(((N 5).descFactorial 0:ℝ)/V^0)*(((N 6).descFactorial 1:ℝ)/V^1)) = V*(d*(1/100)/(1/100)*((N 6:ℝ)/V))
  norm_num
  field_simp

theorem reverse_6 (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (localReaction r d (.inl (6,true))).rate V N =
      V*reverseRate r d (1/100) (1/100) V (concentration V N) 6 := by
  rw [Reaction.rate,prod_seven]
  change (d*(101/8000000000))*V*((((N 0).descFactorial 1:ℝ)/V^1)*(((N 1).descFactorial 1:ℝ)/V^1)*(((N 2).descFactorial 0:ℝ)/V^0)*(((N 3).descFactorial 0:ℝ)/V^0)*(((N 4).descFactorial 0:ℝ)/V^0)*(((N 5).descFactorial 0:ℝ)/V^0)*(((N 6).descFactorial 0:ℝ)/V^0)) = V*(d*(1/8000000000)*(1+1/100)/(1/100)*((N 0:ℝ)/V)*((N 1:ℝ)/V))
  norm_num
  field_simp

theorem local_forward_binding (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) (j : Fin 7) :
    (localReaction r d (.inl (j,false))).rate V N =
      V*forwardRate r d (1/100) (1/100) (concentration V N) j := by
  fin_cases j
  · exact forward_0 r d V hV N
  · exact forward_1 r d V hV N
  · exact forward_2 r d V hV N
  · exact forward_3 r d V hV N
  · exact forward_4 r d V hV N
  · exact forward_5 r d V hV N
  · exact forward_6 r d V hV N

theorem local_reverse_binding (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) (j : Fin 7) :
    (localReaction r d (.inl (j,true))).rate V N =
      V*reverseRate r d (1/100) (1/100) V (concentration V N) j := by
  fin_cases j
  · exact reverse_0 r d V hV N
  · exact reverse_1 r d V hV N
  · exact reverse_2 r d V hV N
  · exact reverse_3 r d V hV N
  · exact reverse_4 r d V hV N
  · exact reverse_5 r d V hV N
  · exact reverse_6 r d V hV N

end
end RAF1519.Refinement
