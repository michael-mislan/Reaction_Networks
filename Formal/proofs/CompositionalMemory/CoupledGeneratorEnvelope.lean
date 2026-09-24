import proofs.CompositionalMemory.CoupledObservables

namespace CompositionalMemory
open FiniteCopy FiniteIntegerRows ControlledRows

noncomputable def coupledCurrent (N : Nat) (data : Nat → Array Int)
    (s : CoupledLiveState N) (k : Fin 2) (col : Nat) : ℝ :=
  (value (data (N+s.1.val)) ((s.2 k).1.val*(4*(N+s.1.val)+1)+(s.2 k).2.val)
    col : ℝ)/(precisionScale : ℝ)

noncomputable def coupledContinuation (N : Nat) (data : Nat → Array Int)
    (s : CoupledLiveState N) (r : CoupledChannel) (k : Fin 2) (col : Nat) : ℝ :=
  let p := coupledProposal N s r
  coupledGridValue (N+p.1.val) data col (p.2 k).1 (p.2 k).2

noncomputable def coupledLocalReturn (N : Nat) (ε : ℝ) (data : Nat → Array Int)
    (s : CoupledLiveState N) (k : Fin 2) (col : Nat) : ℝ :=
  ∑ r : CoupledChannel, coupledRate N ε (some s) r*
    (coupledContinuation N data s r k col-coupledCurrent N data s k col)

theorem coupled_return_envelope (N : Nat) (ε : ℝ) (hε : 0 ≤ ε)
    (data : Nat → Array Int) (word : Fin 2 → Fin 2) (s : CoupledLiveState N)
    (hupper : ∀ (j : Fin (N+1)) k i, i < stateCount (N+j.val) →
      value (data (N+j.val)) i (word k).val ≤ precisionScale) :
    coupledLocalReturn N ε data s 0 (word 0).val+
      coupledLocalReturn N ε data s 1 (word 1).val ≤
      (coupledFiniteModel N ε hε).generator (coupledJointValue N data word) (some s) := by
  apply coupled_generator_lower (coupledFiniteModel N ε hε)
    (coupledJointValue N data word) (some s)
    (coupledCurrent N data s 0 (word 0).val)
    (coupledCurrent N data s 1 (word 1).val)
    (fun r => coupledContinuation N data s r 0 (word 0).val)
    (fun r => coupledContinuation N data s r 1 (word 1).val)
  · rcases s with ⟨j,a⟩
    rfl
  · intro r
    exact coupledJointValue_clipped_lower N data word (coupledProposal N s r).1
      (coupledProposal N s r).2 (hupper (coupledProposal N s r).1)

noncomputable def coupledCurrentTime (N : Nat) (data : Nat → Array Int)
    (s : CoupledLiveState N) (k : Fin 2) : ℝ :=
  if s.1.val=N then 0 else coupledCurrent N data s k 2

noncomputable def coupledTimeContinuation (N : Nat) (data : Nat → Array Int)
    (s : CoupledLiveState N) (r : CoupledChannel) (k : Fin 2) : ℝ :=
  let p := coupledProposal N s r
  coupledGridTime N p.1 data (p.2 k).1 (p.2 k).2

noncomputable def coupledLocalTime (N : Nat) (ε : ℝ) (data : Nat → Array Int)
    (s : CoupledLiveState N) (k : Fin 2) : ℝ :=
  ∑ r : CoupledChannel, coupledRate N ε (some s) r*
    (coupledTimeContinuation N data s r k-coupledCurrentTime N data s k)

theorem coupled_time_envelope (N : Nat) (ε : ℝ) (hε : 0 ≤ ε)
    (data : Nat → Array Int) (s : CoupledLiveState N)
    (hnonneg : ∀ (j : Fin (N+1)) i, i < stateCount (N+j.val) →
      0 ≤ value (data (N+j.val)) i 2) :
    (coupledFiniteModel N ε hε).generator (coupledJointTime N data) (some s) ≤
      (coupledLocalTime N ε data s 0+coupledLocalTime N ε data s 1)/2 := by
  apply coupled_generator_upper (coupledFiniteModel N ε hε)
    (coupledJointTime N data) (some s)
    (coupledCurrentTime N data s 0) (coupledCurrentTime N data s 1)
    (fun r => coupledTimeContinuation N data s r 0)
    (fun r => coupledTimeContinuation N data s r 1)
  · rcases s with ⟨j,a⟩
    by_cases hj : j.val=N
    · simp [coupledJointTime,coupledCurrentTime,hj]
    · simp [coupledJointTime,coupledCurrentTime,coupledCurrent,hj]
      ring
  · intro r
    exact coupledJointTime_clipped_upper N data (coupledProposal N s r).1
      (coupledProposal N s r).2 (hnonneg (coupledProposal N s r).1)

end CompositionalMemory
