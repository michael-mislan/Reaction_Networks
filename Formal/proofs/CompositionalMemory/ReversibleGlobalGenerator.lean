import proofs.CompositionalMemory.ReversibleCheckedGenerator
import proofs.CompositionalMemory.ReversibleArrayBounds

namespace CompositionalMemory
open FiniteCopy FiniteIntegerRows ControlledRows

theorem reversible_checked_generators (N : Nat) (hN : 0 < N) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10) (data : Nat → Array Int)
    (hrows : ∀ m, N ≤ m → m < 2*N → ReversibleRows.checkLayer m (data m) (data (m+1))=true)
    (ht : ReversibleRows.terminalCheck N (data (2*N))=true) (word : Fin 2 → Fin 2) :
    (∀ s, -(2/1000000 : ℝ) ≤
      (reversibleFiniteModel N ε hε).generator (coupledJointValue N data word) s) ∧
    (∀ s, (reversibleFiniteModel N ε hε).generator (coupledJointTime N data) s ≤
      -(5/8 : ℝ)*coupledJointTime N data s+1/50000) := by
  have hupper (j : Fin (N+1)) (k : Fin 2) (i : Nat) (hi : i < stateCount (N+j.val)) :=
    (ReversibleRows.all_array_bounds N data hrows ht j i hi).1 (word k)
  have hnonneg (j : Fin (N+1)) (i : Nat) (hi : i < stateCount (N+j.val)) :
      0 ≤ value (data (N+j.val)) i 2 := by
    exact (show (0 : Int) ≤ precisionScale by norm_num [precisionScale]).trans
      (ReversibleRows.all_array_bounds N data hrows ht j i hi).2
  have hl (s : CoupledLiveState N) (hs : s.1.val < N) (k : Fin 2) (col : Fin 2) :
      -(1/1000000 : ℝ) ≤ reversibleControlledLocal N ε data s k col.val := by
    have hh := reversible_checked_local_bounds N hN ε hε hε1 data hrows s hs k
    fin_cases col
    · exact hh.1
    · exact hh.2.1
  constructor
  · intro s
    cases s with
    | none => norm_num [FiniteJumpModel.generator,reversibleFiniteModel,reversibleRate]
    | some s =>
      rcases s with ⟨j,a⟩
      by_cases hj : j.val=N
      · norm_num [FiniteJumpModel.generator,reversibleFiniteModel,reversibleRate,hj]
      · have hs : j.val < N := by omega
        have he := reversible_return_envelope N ε hε data word ⟨j,a⟩ hupper
        rw [reversible_return_controlled,reversible_return_controlled] at he
        linarith only [he,hl ⟨j,a⟩ hs 0 (word 0),hl ⟨j,a⟩ hs 1 (word 1)]
  · intro s
    cases s with
    | none => norm_num [FiniteJumpModel.generator,reversibleFiniteModel,reversibleRate,coupledJointTime]
    | some s =>
      rcases s with ⟨j,a⟩
      by_cases hj : j.val=N
      · norm_num [FiniteJumpModel.generator,reversibleFiniteModel,reversibleRate,coupledJointTime,hj]
      · have hs : j.val < N := by omega
        have he := reversible_time_envelope N ε hε data ⟨j,a⟩ hnonneg
        have h0 := reversible_time_controlled N ε hε data ⟨j,a⟩ 0 hj hnonneg
        have h1 := reversible_time_controlled N ε hε data ⟨j,a⟩ 1 hj hnonneg
        have b0 := (reversible_checked_local_bounds N hN ε hε hε1 data hrows ⟨j,a⟩ hs 0).2.2
        have b1 := (reversible_checked_local_bounds N hN ε hε hε1 data hrows ⟨j,a⟩ hs 1).2.2
        have hw : coupledJointTime N data (some ⟨j,a⟩)=
            (coupledCurrent N data ⟨j,a⟩ 0 2+coupledCurrent N data ⟨j,a⟩ 1 2)/2 := by
          simp [coupledJointTime,coupledCurrent,hj]
          ring
        rw [hw]
        linarith only [he,h0,h1,b0,b1]

end CompositionalMemory
