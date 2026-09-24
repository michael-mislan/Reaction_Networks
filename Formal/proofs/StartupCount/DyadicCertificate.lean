import proofs.StartupCount.PowerGenerator
import Mathlib.Algebra.Order.Floor.Semiring

namespace StartupCount
noncomputable section
set_option maxHeartbeats 40000

def countCut (V : ℝ) : ℕ := ⌊V/2000000000000000000⌋₊
def stockThreshold (V : ℝ) : ℕ := ⌈V/3000000000000000000⌉₊
def dyadicIndex (V : ℝ) : ℕ := ⌊V/100000000000000000000⌋₊

theorem count_rounding_bounds (V : ℝ) (hV : 1000000000000000000000000 ≤ V) :
    10 ≤ countCut V ∧ (countCut V : ℝ) ≤ V/2000000000000000000 ∧
    100 ≤ dyadicIndex V ∧ 10*dyadicIndex V ≤ countCut V-stockThreshold V-1 ∧
    stockThreshold V+1 ≤ 100*(dyadicIndex V+1) ∧
    (countCut V : ℝ) ≤ V/100000000000000000 := by
  have hv : 0 ≤ V := by linarith
  have hm := Nat.floor_le (show 0 ≤ V/2000000000000000000 by positivity)
  have hm' := Nat.lt_floor_add_one (V/2000000000000000000)
  have hh := Nat.ceil_lt_add_one (show 0 ≤ V/3000000000000000000 by positivity)
  have hN := Nat.floor_le (show 0 ≤ V/100000000000000000000 by positivity)
  have hN' := Nat.lt_floor_add_one (V/100000000000000000000)
  change (countCut V : ℝ) ≤ _ at hm
  change V/2000000000000000000 < (countCut V : ℝ)+1 at hm'
  change (stockThreshold V : ℝ) < V/3000000000000000000+1 at hh
  change (dyadicIndex V : ℝ) ≤ _ at hN
  change V/100000000000000000000 < (dyadicIndex V : ℝ)+1 at hN'
  have hm10 : 10 ≤ countCut V := by
    apply (Nat.le_floor_iff (show 0 ≤ V/2000000000000000000 by positivity)).mpr
    norm_num
    linarith
  have hN100 : 100 ≤ dyadicIndex V := by
    apply (Nat.le_floor_iff (show 0 ≤ V/100000000000000000000 by positivity)).mpr
    norm_num
    linarith
  have hgap : 10*dyadicIndex V+stockThreshold V+1 ≤ countCut V := by
    have he : (10 : ℝ)*dyadicIndex V+stockThreshold V+1 ≤ countCut V := by linarith
    exact_mod_cast he
  have hhN : stockThreshold V+1 ≤ 100*(dyadicIndex V+1) := by
    have he : (stockThreshold V : ℝ)+1 ≤ 100*((dyadicIndex V : ℝ)+1) := by linarith
    exact_mod_cast he
  exact ⟨hm10,hm,hN100,by omega,hhN,by linarith⟩

theorem dyadic_decay (N : ℕ) (hN : 100 ≤ N) :
    ((N : ℝ)+1)*(1/2 : ℝ)^N ≤ 101*(1/2 : ℝ)^100 := by
  induction N,hN using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hp : 0 ≤ (1/2 : ℝ)^k := by positivity
    have hh := mul_le_mul_of_nonneg_right
      (show ((k : ℝ)+2)*(1/2) ≤ (k : ℝ)+1 by linarith) hp
    push_cast
    rw [pow_succ]
    nlinarith only [hh,ih]

/-- Only a tenth power and a hundredth dyadic power are computed. -/
theorem dyadic_crossing_certificate (m h N : ℕ) (hN : 100 ≤ N)
    (hgap : 10*N ≤ m-h-1) (hh : h+1 ≤ 100*(N+1)) :
    10*(1+1476*(h+1 : ℕ)*198)*(9/10 : ℝ)^(m-h-1) < 1/1000000 := by
  have hpow : (9/10 : ℝ)^(m-h-1) ≤ (1/2 : ℝ)^N := by
    apply le_trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hgap)
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) N
  have hhR : (h+1 : ℕ) ≤ (100 : ℝ)*(N+1 : ℕ) := by exact_mod_cast hh
  have hpre : 10*(1+1476*(h+1 : ℕ)*198) ≤ (300000000 : ℝ)*((N : ℝ)+1) := by
    push_cast at hhR ⊢
    have hn : (0 : ℝ) ≤ N := by positivity
    linarith
  calc
    _ ≤ (300000000 : ℝ)*((N : ℝ)+1)*(1/2 : ℝ)^N :=
      mul_le_mul hpre hpow (by positivity) (by positivity)
    _ = 300000000*(((N : ℝ)+1)*(1/2 : ℝ)^N) := by ring
    _ ≤ 300000000*(101*(1/2 : ℝ)^100) :=
      mul_le_mul_of_nonneg_left (dyadic_decay N hN) (by norm_num)
    _ < _ := by norm_num

theorem uniform_crossing_scalar_certificate (V : ℝ) (hV : 1000000000000000000000000 ≤ V) :
    10*(1+1476*(stockThreshold V+1 : ℕ)*198)*
      (9/10 : ℝ)^(countCut V-stockThreshold V-1) < 1/1000000 := by
  obtain ⟨_,_,hN,hgap,hh,_⟩ := count_rounding_bounds V hV
  exact dyadic_crossing_certificate _ _ _ hN hgap hh

end
end StartupCount
