import proofs.CompositionalMemory.CoupledFiniteSource
import proofs.CompositionalMemory.ControlledCheckedRows

namespace CompositionalMemory
open FiniteIntegerRows ControlledRows
set_option maxHeartbeats 80000

noncomputable def coupledGridValue (m : Nat) (data : Nat → Array Int) (col : Nat)
    (x y : Int) : ℝ :=
  (target m (data m) x y col 0 : ℝ)/(precisionScale : ℝ)

noncomputable def coupledJointValue (N : Nat) (data : Nat → Array Int)
    (word : Fin 2 → Fin 2) : CoupledFiniteState N → ℝ
  | none => 0
  | some ⟨j,a⟩ =>
    (value (data (N+j.val)) ((a 0).1.val*(4*(N+j.val)+1)+(a 0).2.val)
      (word 0).val : ℝ)/(precisionScale : ℝ)+
    (value (data (N+j.val)) ((a 1).1.val*(4*(N+j.val)+1)+(a 1).2.val)
      (word 1).val : ℝ)/(precisionScale : ℝ)-1

noncomputable def coupledJointTime (N : Nat) (data : Nat → Array Int) :
    CoupledFiniteState N → ℝ
  | none => 0
  | some ⟨j,a⟩ => if j.val=N then 0 else
    ((value (data (N+j.val)) ((a 0).1.val*(4*(N+j.val)+1)+(a 0).2.val) 2 : ℝ)+
    (value (data (N+j.val)) ((a 1).1.val*(4*(N+j.val)+1)+(a 1).2.val) 2 : ℝ))/
      (2*(precisionScale : ℝ))

noncomputable def coupledGridTime (N : Nat) (j : Fin (N+1))
    (data : Nat → Array Int) (x y : Int) : ℝ :=
  if j.val=N then 0 else
    (target (N+j.val) (data (N+j.val)) x y 2 precisionScale : ℝ)/(precisionScale : ℝ)

theorem grid_index_lt (m : Nat) (x y : Int)
    (hx : 0 ≤ x ∧ x ≤ 16*(m : Int)) (hy : 0 ≤ y ∧ y ≤ 4*(m : Int)) :
    x.toNat*(4*m+1)+y.toNat < stateCount m := by
  have hx' : x.toNat ≤ 16*m := by omega
  have hy' : y.toNat ≤ 4*m := by omega
  have hh := Nat.mul_le_mul_right (4*m+1) hx'
  dsimp [stateCount]
  nlinarith only [hh,hy']

theorem coupledGridValue_upper (m : Nat) (data : Nat → Array Int) (col : Nat)
    (h : ∀ i, i < stateCount m → value (data m) i col ≤ precisionScale)
    (x y : Int) : coupledGridValue m data col x y ≤ 1 := by
  unfold coupledGridValue target
  split_ifs with hxy
  · apply (div_le_one (by norm_num [precisionScale])).mpr
    exact_mod_cast h _ (grid_index_lt m x y ⟨hxy.1,hxy.2.1⟩ hxy.2.2)
  · norm_num

/-- A global exit raises the sum-minus-one continuation, provided each local
return value is at most one. This is the critical coupling boundary check. -/
theorem coupledJointValue_clipped_lower (N : Nat) (data : Nat → Array Int)
    (word : Fin 2 → Fin 2) (j : Fin (N+1)) (a : Fin 2 → Int × Int)
    (hupper : ∀ k i, i < stateCount (N+j.val) →
      value (data (N+j.val)) i (word k).val ≤ precisionScale) :
    coupledGridValue (N+j.val) data (word 0).val (a 0).1 (a 0).2+
      coupledGridValue (N+j.val) data (word 1).val (a 1).1 (a 1).2-1 ≤
      coupledJointValue N data word (coupledClipped N j a) := by
  have hu0 := coupledGridValue_upper (N+j.val) data (word 0).val (hupper 0) (a 0).1 (a 0).2
  have hu1 := coupledGridValue_upper (N+j.val) data (word 1).val (hupper 1) (a 1).1 (a 1).2
  unfold coupledClipped
  split_ifs with ha
  · have h0 := ha 0
    have h1 := ha 1
    simp only [coupledJointValue,coupledGridValue,target,Nat.cast_add]
    simp [h0,h1]
  · have hex : ¬ (∀ k, 0 ≤ (a k).1 ∧ (a k).1 ≤ 16*((N : Int)+j.val) ∧
        0 ≤ (a k).2 ∧ (a k).2 ≤ 4*((N : Int)+j.val)) := ha
    obtain ⟨k,hk⟩ := not_forall.mp hex
    have hz : coupledGridValue (N+j.val) data (word k).val (a k).1 (a k).2=0 := by
      unfold coupledGridValue target
      have hn : ¬(0 ≤ (a k).1 ∧ (a k).1 ≤ 16*((N : Int)+j.val) ∧
        0 ≤ (a k).2 ∧ (a k).2 ≤ 4*((N : Int)+j.val)) := hk
      simp [Nat.cast_add,hn]
    change _ ≤ 0
    fin_cases k <;> simp only [Fin.zero_eta,Fin.mk_one] at hz <;> linarith

theorem coupledGridTime_nonneg (N : Nat) (j : Fin (N+1)) (data : Nat → Array Int)
    (h : ∀ i, i < stateCount (N+j.val) → 0 ≤ value (data (N+j.val)) i 2)
    (x y : Int) : 0 ≤ coupledGridTime N j data x y := by
  unfold coupledGridTime
  split_ifs
  · rfl
  · apply div_nonneg _ (by norm_num [precisionScale])
    unfold target
    split_ifs with hxy
    · exact_mod_cast h _ (grid_index_lt (N+j.val) x y ⟨hxy.1,hxy.2.1⟩ hxy.2.2)
    · norm_num [precisionScale]

theorem coupledJointTime_clipped_upper (N : Nat) (data : Nat → Array Int)
    (j : Fin (N+1)) (a : Fin 2 → Int × Int)
    (h : ∀ i, i < stateCount (N+j.val) → 0 ≤ value (data (N+j.val)) i 2) :
    coupledJointTime N data (coupledClipped N j a) ≤
      (coupledGridTime N j data (a 0).1 (a 0).2+
       coupledGridTime N j data (a 1).1 (a 1).2)/2 := by
  have h0 := coupledGridTime_nonneg N j data h (a 0).1 (a 0).2
  have h1 := coupledGridTime_nonneg N j data h (a 1).1 (a 1).2
  unfold coupledClipped
  split_ifs with ha
  · have ha0 := ha 0
    have ha1 := ha 1
    by_cases hj : j.val=N
    · simp [coupledJointTime,coupledGridTime,hj]
    · simp [coupledJointTime,coupledGridTime,hj,target,Nat.cast_add,ha0,ha1]
      ring_nf
      exact le_rfl
  · change 0 ≤ _
    positivity

end CompositionalMemory
