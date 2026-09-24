import proofs.CompositionalMemory.ReversibleFiniteSource

namespace CompositionalMemory
open FiniteCopy
set_option maxHeartbeats 500000

def reversibleRateCap : Fin 13 → ℝ :=
  ![40,6220,3840,6400,840,2,7,2,1,3,960,1,1]

theorem reversible_rate_cap (N : Nat) (hN : 0 < N) (ε : ℝ)
    (hε1 : ε ≤ 1/10) (j : Fin (N+1))
    (a : Fin 2 → Fin (16*(N+j.val)+1) × Fin (4*(N+j.val)+1))
    (k : Fin 2) (r : Fin 13) :
    reversibleRate N ε (some ⟨j,a⟩) (k,r) ≤ reversibleRateCap r*(N+j.val) := by
  by_cases hj : j.val=N
  · fin_cases r <;> norm_num [reversibleRate,reversibleRateCap,hj]
  let m : ℝ := N+j.val
  let x : ℝ := (a k).1.val
  let y : ℝ := (a k).2.val
  let z : ℝ := (a ⟨1-k.val,by omega⟩).2.val
  let q : ℝ := ((a k).1.val*((a k).1.val-1) : Nat)
  have hm : 0 < m := by dsimp [m]; exact_mod_cast (show 0 < N+j.val by omega)
  have hx : 0 ≤ x := Nat.cast_nonneg _
  have hy : 0 ≤ y := Nat.cast_nonneg _
  have hz : 0 ≤ z := Nat.cast_nonneg _
  have hxu : x ≤ 16*m := by
    have hh := Nat.le_of_lt_succ (a k).1.isLt
    dsimp [x,m]; exact_mod_cast hh
  have hyu : y ≤ 4*m := by
    have hh := Nat.le_of_lt_succ (a k).2.isLt
    dsimp [y,m]; exact_mod_cast hh
  have hzu : z ≤ 4*m := by
    have hh := Nat.le_of_lt_succ (a ⟨1-k.val,by omega⟩).2.isLt
    dsimp [z,m]; exact_mod_cast hh
  have hq : q ≤ x*x := by
    have hs : (((a k).1.val-1 : Nat) : ℝ) ≤ x := by
      exact Nat.cast_le.mpr (Nat.sub_le (a k).1.val 1)
    dsimp only [q]
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hs hx
  have hxx : x*x ≤ 256*(m*m) := by
    have hh := mul_self_le_mul_self hx hxu
    nlinarith only [hh]
  have hxy : x*y ≤ 64*(m*m) := by
    have hh := mul_le_mul hxu hyu hy (by positivity : 0 ≤ 16*m)
    nlinarith only [hh]
  have hxz : x*z ≤ 64*(m*m) := by
    have hh := mul_le_mul hxu hzu hz (by positivity : 0 ≤ 16*m)
    nlinarith only [hh]
  have hyz : y*z ≤ 16*(m*m) := by
    have hh := mul_le_mul hyu hzu hz (by positivity : 0 ≤ 4*m)
    nlinarith only [hh]
  have hqd : q/m ≤ 256*m := (div_le_iff₀ hm).mpr (by nlinarith only [hq,hxx])
  have hxyd : x*y/m ≤ 64*m := (div_le_iff₀ hm).mpr (by nlinarith only [hxy])
  have hxzd : x*z/m ≤ 64*m := (div_le_iff₀ hm).mpr (by nlinarith only [hxz])
  have hyzd : y*z/m ≤ 16*m := (div_le_iff₀ hm).mpr (by nlinarith only [hyz])
  have heX := mul_le_mul_of_nonneg_right hε1 (div_nonneg (mul_nonneg hx hz) hm.le)
  have heY := mul_le_mul_of_nonneg_right hε1 (div_nonneg (mul_nonneg hy hz) hm.le)
  have hEX : ε*(x*z/m) ≤ (32/5)*m := by nlinarith only [heX,hxzd]
  have hEY : ε*(y*z/m) ≤ (8/5)*m := by nlinarith only [heY,hyzd]
  simp only [reversibleRate,reversibleRateCap,hj,if_false]
  change (![193/5*m,1555*y,15*q/m,100*x*y/m,105/2*x,x/10,
    ε*x*z/m,ε*y*z/m,193/750000*x,311/30000*q/m,15*x*y/m,(1/1000)*y,21/40000*m] r) ≤
    (![40,6220,3840,6400,840,2,7,2,1,3,960,1,1] r)*m
  fin_cases r <;> norm_num <;>
    ring_nf at hqd hxyd hEX hEY ⊢ <;>
    nlinarith only [hm,hxu,hyu,hqd,hxyd,hEX,hEY]


theorem reversible_total_rate_cap (N : Nat) (hN : 0 < N) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10) (s : CoupledFiniteState N) :
    (reversibleFiniteModel N ε hε).total s ≤ 73268*N := by
  cases s with
  | none => simp [FiniteJumpModel.total,reversibleFiniteModel,reversibleRate]
  | some s =>
    rcases s with ⟨j,a⟩
    have hh : (reversibleFiniteModel N ε hε).total (some ⟨j,a⟩) ≤
        ∑ r : ReversibleChannel,reversibleRateCap r.2*((N : ℝ)+j.val) := by
      apply Finset.sum_le_sum
      intro r _
      exact reversible_rate_cap N hN ε hε1 j a r.1 r.2
    have hs : (∑ r : ReversibleChannel,reversibleRateCap r.2*((N : ℝ)+j.val))=
        36634*((N : ℝ)+j.val) := by
      norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,reversibleRateCap]
      ring
    have hj : (j.val : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt_succ j.isLt
    rw [hs] at hh
    linarith

end CompositionalMemory
