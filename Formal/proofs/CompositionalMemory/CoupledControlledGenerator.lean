import proofs.CompositionalMemory.CoupledGridIdentities

namespace CompositionalMemory
open FiniteCopy FiniteIntegerRows ControlledRows

noncomputable def coupledGridObservable (m : Nat) (data : Nat → Array Int)
    (col : Nat) (x y : Int) : ℝ :=
  (target m (data m) x y col (if col=2 then precisionScale else 0) : ℝ)/
    (precisionScale : ℝ)

noncomputable def coupledControlledLocal (N : Nat) (ε : ℝ) (data : Nat → Array Int)
    (s : CoupledLiveState N) (k : Fin 2) (col : Nat) : ℝ :=
  ∑ r : CoupledChannel, coupledRate N ε (some s) r*
    (let p := coupledProposal N s r
     coupledGridObservable (N+p.1.val) data col (p.2 k).1 (p.2 k).2-
       coupledCurrent N data s k col)

theorem coupled_return_controlled (N : Nat) (ε : ℝ) (data : Nat → Array Int)
    (s : CoupledLiveState N) (k : Fin 2) (col : Fin 2) :
    coupledLocalReturn N ε data s k col.val=coupledControlledLocal N ε data s k col.val := by
  have hc : col.val ≠ 2 := by omega
  simp [coupledLocalReturn,coupledControlledLocal,coupledContinuation,
    coupledGridObservable,coupledGridValue,hc]

theorem coupled_time_controlled (N : Nat) (ε : ℝ) (hε : 0 ≤ ε)
    (data : Nat → Array Int) (s : CoupledLiveState N) (k : Fin 2)
    (hs : s.1.val ≠ N)
    (hnonneg : ∀ (j : Fin (N+1)) i, i < stateCount (N+j.val) →
      0 ≤ value (data (N+j.val)) i 2) :
    coupledLocalTime N ε data s k ≤ coupledControlledLocal N ε data s k 2 := by
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_left _ (coupledRate_nonneg N ε hε (some s) r)
  simp only [coupledCurrentTime,hs,ite_false]
  apply sub_le_sub_right
  dsimp only [coupledTimeContinuation]
  let p := coupledProposal N s r
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

theorem coupledGridObservable_natural (m : Nat) (data : Nat → Array Int) (col x y : Nat)
    (hx : x ≤ 16*m) (hy : y ≤ 4*m) :
    coupledGridObservable m data col x y=
      (value (data m) (x*(4*m+1)+y) col : ℝ)/(precisionScale : ℝ) := by
  have hx' : (x : Int) ≤ 16*(m : Int) := by exact_mod_cast hx
  have hy' : (y : Int) ≤ 4*(m : Int) := by exact_mod_cast hy
  simp [coupledGridObservable,target,hx',hy']

theorem coupledGridObservable_growth (m : Nat) (data : Nat → Array Int) (col x y : Nat)
    (hx : x ≤ 16*m) (hy : y ≤ 4*m) (hpos : 0 < x) :
    coupledGridObservable (m+1) data col ((x : Int)-1) y=
      (value (data (m+1)) ((x-1)*(4*(m+1)+1)+y) col : ℝ)/(precisionScale : ℝ) := by
  have he : ((x-1 : Nat) : Int)=(x : Int)-1 := by omega
  rw [← he]
  exact coupledGridObservable_natural (m+1) data col (x-1) y (by omega) (by omega)

end CompositionalMemory
