import proofs.CompositionalMemory.CoupledControlledGenerator

namespace CompositionalMemory
open FiniteIntegerRows ControlledRows
set_option maxHeartbeats 400000

theorem coupled_local_controlled_literal (N : Nat) (hN : 0 < N) (ε : ℝ)
    (data : Nat → Array Int) (s : CoupledLiveState N) (hs : s.1.val < N)
    (k : Fin 2) (col : Nat) :
    coupledControlledLocal N ε data s k col=
      literal (N+s.1.val) (data (N+s.1.val)) (data (N+s.1.val+1))
        ((s.2 k).1.val*(4*(N+s.1.val)+1)+(s.2 k).2.val) col
        ((s.2 ⟨1-k.val,by omega⟩).1.val/(16*((N+s.1.val : Nat) : ℝ)))
        (5*ε*(s.2 ⟨1-k.val,by omega⟩).2.val/(2*((N+s.1.val : Nat) : ℝ))) := by
  rcases s with ⟨j,a⟩
  change j.val < N at hs
  have hj : j.val ≠ N := by omega
  have hm : (0 : ℝ) < (N : ℝ)+j.val := by positivity
  have hx (u : Fin 2) : (a u).1.val ≤ 16*(N+j.val) := Nat.le_of_lt_succ (a u).1.isLt
  have hy (u : Fin 2) : (a u).2.val ≤ 4*(N+j.val) := Nat.le_of_lt_succ (a u).2.isLt
  have hi (u : Fin 2) := coupled_index_coordinates (N+j.val) (a u).1.val (a u).2.val (hy u)
  have hc (u : Fin 2) := coupledGridObservable_natural (N+j.val) data col
    (a u).1.val (a u).2.val (hx u) (hy u)
  have hg (u : Fin 2) := coupledGridObservable_natural (N+j.val+1) data col
    (a u).1.val (a u).2.val (by have := hx u; omega) (by have := hy u; omega)
  have ho (u : Fin 2) (hp : 0 < (a u).1.val) := coupledGridObservable_growth (N+j.val)
    data col (a u).1.val (a u).2.val (hx u) (hy u) hp
  have hpos (u : Fin 2) (hh : (a u).1 ≠ 0) : 0 < (a u).1.val := by
    have hn : (a u).1.val ≠ 0 := by intro he; apply hh; exact Fin.ext he
    omega
  have hcast (u : Fin 2) (hh : (a u).1 ≠ 0) :
      (((a u).1.val-1 : Nat) : ℝ)=((a u).1.val : ℝ)-1 := by
    rw [Nat.cast_sub (show 1 ≤ (a u).1.val by have hp := hpos u hh; omega)]
    norm_num
  fin_cases k <;>
    simp only [coupledControlledLocal,Fintype.sum_prod_type,Fin.sum_univ_succ] <;>
    norm_num [coupledRate,coupledProposal,hj,Function.update,
      coupledCurrent,literal,hi,Nat.add_assoc] <;>
    simp only [hc]
  all_goals
    simp only [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    by_cases h0 : (a 0).1=0 <;> by_cases h1 : (a 1).1=0
    all_goals
      have hg0 := hg 0
      have hg1 := hg 1
      have ho0 : (a 0).1 ≠ 0 → _ := fun hh => ho 0 (hpos 0 hh)
      have ho1 : (a 1).1 ≠ 0 → _ := fun hh => ho 1 (hpos 1 hh)
      norm_num [h0,h1,Nat.add_assoc] at hg0 hg1 ho0 ho1
      norm_num [h0,h1,Function.update,Nat.add_assoc,hg0,hg1,ho0,ho1,hcast]
      simp only [coupledGridObservable]
      field_simp
      ring

end CompositionalMemory
