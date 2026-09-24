import proofs.CompositionalMemory.ReversibleFiniteSource
import proofs.CompositionalMemory.CoupledControlledGenerator

namespace CompositionalMemory
open FiniteCopy FiniteIntegerRows ControlledRows

noncomputable def reversibleContinuation (N : Nat) (data : Nat → Array Int)
    (s : CoupledLiveState N) (r : ReversibleChannel) (k : Fin 2) (col : Nat) : ℝ :=
  let p := reversibleProposal N s r
  coupledGridValue (N+p.1.val) data col (p.2 k).1 (p.2 k).2

noncomputable def reversibleLocalReturn (N : Nat) (ε : ℝ) (data : Nat → Array Int)
    (s : CoupledLiveState N) (k : Fin 2) (col : Nat) : ℝ :=
  ∑ r : ReversibleChannel,reversibleRate N ε (some s) r*
    (reversibleContinuation N data s r k col-coupledCurrent N data s k col)

theorem reversible_return_envelope (N : Nat) (ε : ℝ) (hε : 0 ≤ ε)
    (data : Nat → Array Int) (word : Fin 2 → Fin 2) (s : CoupledLiveState N)
    (hupper : ∀ (j : Fin (N+1)) k i, i < stateCount (N+j.val) →
      value (data (N+j.val)) i (word k).val ≤ precisionScale) :
    reversibleLocalReturn N ε data s 0 (word 0).val+
      reversibleLocalReturn N ε data s 1 (word 1).val ≤
      (reversibleFiniteModel N ε hε).generator (coupledJointValue N data word) (some s) := by
  apply coupled_generator_lower (reversibleFiniteModel N ε hε)
    (coupledJointValue N data word) (some s)
    (coupledCurrent N data s 0 (word 0).val)
    (coupledCurrent N data s 1 (word 1).val)
    (fun r => reversibleContinuation N data s r 0 (word 0).val)
    (fun r => reversibleContinuation N data s r 1 (word 1).val)
  · rcases s with ⟨j,a⟩
    rfl
  · intro r
    exact coupledJointValue_clipped_lower N data word (reversibleProposal N s r).1
      (reversibleProposal N s r).2 (hupper (reversibleProposal N s r).1)

noncomputable def reversibleTimeContinuation (N : Nat) (data : Nat → Array Int)
    (s : CoupledLiveState N) (r : ReversibleChannel) (k : Fin 2) : ℝ :=
  let p := reversibleProposal N s r
  coupledGridTime N p.1 data (p.2 k).1 (p.2 k).2

noncomputable def reversibleLocalTime (N : Nat) (ε : ℝ) (data : Nat → Array Int)
    (s : CoupledLiveState N) (k : Fin 2) : ℝ :=
  ∑ r : ReversibleChannel,reversibleRate N ε (some s) r*
    (reversibleTimeContinuation N data s r k-coupledCurrentTime N data s k)

theorem reversible_time_envelope (N : Nat) (ε : ℝ) (hε : 0 ≤ ε)
    (data : Nat → Array Int) (s : CoupledLiveState N)
    (hnonneg : ∀ (j : Fin (N+1)) i, i < stateCount (N+j.val) →
      0 ≤ value (data (N+j.val)) i 2) :
    (reversibleFiniteModel N ε hε).generator (coupledJointTime N data) (some s) ≤
      (reversibleLocalTime N ε data s 0+reversibleLocalTime N ε data s 1)/2 := by
  apply coupled_generator_upper (reversibleFiniteModel N ε hε)
    (coupledJointTime N data) (some s)
    (coupledCurrentTime N data s 0) (coupledCurrentTime N data s 1)
    (fun r => reversibleTimeContinuation N data s r 0)
    (fun r => reversibleTimeContinuation N data s r 1)
  · rcases s with ⟨j,a⟩
    by_cases hj : j.val=N
    · simp [coupledJointTime,coupledCurrentTime,hj]
    · simp [coupledJointTime,coupledCurrentTime,coupledCurrent,hj]
      ring
  · intro r
    exact coupledJointTime_clipped_upper N data (reversibleProposal N s r).1
      (reversibleProposal N s r).2 (hnonneg (reversibleProposal N s r).1)

noncomputable def reversibleControlledLocal (N : Nat) (ε : ℝ) (data : Nat → Array Int)
    (s : CoupledLiveState N) (k : Fin 2) (col : Nat) : ℝ :=
  ∑ r : ReversibleChannel,reversibleRate N ε (some s) r*
    (let p := reversibleProposal N s r
     coupledGridObservable (N+p.1.val) data col (p.2 k).1 (p.2 k).2-
       coupledCurrent N data s k col)

theorem reversible_return_controlled (N : Nat) (ε : ℝ) (data : Nat → Array Int)
    (s : CoupledLiveState N) (k : Fin 2) (col : Fin 2) :
    reversibleLocalReturn N ε data s k col.val=reversibleControlledLocal N ε data s k col.val := by
  have hc : col.val ≠ 2 := by omega
  simp [reversibleLocalReturn,reversibleControlledLocal,reversibleContinuation,
    coupledGridObservable,coupledGridValue,hc]

theorem reversible_time_controlled (N : Nat) (ε : ℝ) (hε : 0 ≤ ε)
    (data : Nat → Array Int) (s : CoupledLiveState N) (k : Fin 2)
    (hs : s.1.val ≠ N)
    (hnonneg : ∀ (j : Fin (N+1)) i, i < stateCount (N+j.val) →
      0 ≤ value (data (N+j.val)) i 2) :
    reversibleLocalTime N ε data s k ≤ reversibleControlledLocal N ε data s k 2 := by
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_left _ (reversibleRate_nonneg N ε hε (some s) r)
  simp only [coupledCurrentTime,hs,ite_false]
  apply sub_le_sub_right
  dsimp only [reversibleTimeContinuation]
  let p := reversibleProposal N s r
  change coupledGridTime N p.1 data (p.2 k).1 (p.2 k).2 ≤
    coupledGridObservable (N+p.1.val) data 2 (p.2 k).1 (p.2 k).2
  unfold coupledGridTime coupledGridObservable
  simp only
  split_ifs
  · apply div_nonneg _ (by norm_num [precisionScale])
    unfold target
    split_ifs with hxy
    · exact_mod_cast hnonneg p.1 _
        (grid_index_lt _ _ _ ⟨hxy.1,hxy.2.1⟩ hxy.2.2)
    · norm_num [precisionScale]
  · exact le_rfl

end CompositionalMemory
