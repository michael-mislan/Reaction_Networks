import proofs.RandomViability.BindingCompetitionTimed
import proofs.RandomViability.BindingCompetitionThroughput

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

theorem competition_grid_sum (E : ℝ → ℝ) (J : ℝ) (m k n : ℕ)
    (hgrid : ∀ i : ℕ,i < m → J  ≤  E ((i:ℝ)+1)-E i) (hkn : k+n ≤ m) :
    J*(n:ℝ)  ≤  E (k+n:ℕ)-E k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := ih (by omega)
    have hi := hgrid (k+n) (by omega)
    push_cast at hh hi ⊢
    simp only [add_assoc] at hi
    linarith

/-- All alignments hold on one trajectory; no additional probability union. -/
theorem competition_arbitrary_interval (E : ℝ → ℝ) (hE : Monotone E) (J : ℝ) (m : ℕ)
    (hgrid : ∀ i : ℕ,i < m → J  ≤  E ((i:ℝ)+1)-E i)
    (s L : ℝ) (hs : 0 ≤ s) (hL : 0 ≤ L) (hend : s+L ≤ m) :
    J*((⌊L⌋₊-1:ℕ):ℝ)  ≤  E (s+L)-E s := by
  by_cases hn : ⌊L⌋₊ ≤ 1
  · have hz : ⌊L⌋₊-1=0 := by omega
    rw [hz,Nat.cast_zero,mul_zero]
    exact sub_nonneg.mpr (hE (by linarith))
  · let k := ⌈s⌉₊
    let n := ⌊L⌋₊-1
    have hk : s ≤ (k:ℝ) := Nat.le_ceil s
    have hk1 : (k:ℝ) < s+1 := Nat.ceil_lt_add_one hs
    have hn1 : (n:ℝ)=(⌊L⌋₊:ℝ)-1 := by
      dsimp [n]
      rw [Nat.cast_sub (by omega),Nat.cast_one]
    have hf := Nat.floor_le hL
    have he : (k:ℝ)+(n:ℝ) ≤ s+L := by linarith
    have hkn : k+n ≤ m := by exact_mod_cast he.trans hend
    have hh := competition_grid_sum E J m k n hgrid hkn
    have hl := hE hk
    have hr := hE he
    push_cast at hh
    change J*(n:ℝ) ≤ _
    linarith

theorem competition_two_time_units (E : ℝ → ℝ) (hE : Monotone E) (J : ℝ) (m : ℕ)
    (hgrid : ∀ i : ℕ,i < m → J  ≤  E ((i:ℝ)+1)-E i)
    (s : ℝ) (hs : 0 ≤ s) (hend : s+2 ≤ m) : J  ≤  E (s+2)-E s := by
  have hh := competition_arbitrary_interval E hE J m hgrid s 2 hs (by norm_num) hend
  norm_num at hh
  exact hh

theorem competition_service_ratio (V m T E Q : ℝ) (hV : 0 < V) (hm : 0 < m) (hT : 0 ≤ T)
    (hQ : Q ≤ V*T/8) (hE : V*m/5000 ≤ E) : Q/E  ≤  625*T/m := by
  have hE0 : 0 < E := lt_of_lt_of_le (by positivity) hE
  have hprod := mul_le_mul_of_nonneg_left hE (show 0 ≤ 625*T/m by positivity)
  have he : (625*T/m)*(V*m/5000)=V*T/8 := by field_simp; ring
  rw [he] at hprod
  exact (div_le_iff₀ hE0).mpr (hQ.trans hprod)

theorem competition_recovery_ratio (V m T E food : ℝ) (hV : 0 < V) (hm : 0 ≤ m)
    (hT : 0 ≤ T) (hf : 0 ≤ food) (hfood : food ≤ 8*V*T) (hE : V*m/5000 ≤ E) :
    m/(5000*(4+8*T))  ≤  E/(4*V+food) := by
  have hd : 0 < 4*V+food := by positivity
  have hden : 0 < 5000*(4+8*T) := by positivity
  have hp := mul_le_mul_of_nonneg_left hfood (show 0 ≤ m/(5000*(4+8*T)) by positivity)
  have he : m/(5000*(4+8*T))*(4*V+8*V*T)=V*m/5000 := by field_simp
  apply (le_div_iff₀ hd).mpr
  calc
    _  ≤  m/(5000*(4+8*T))*(4*V+8*V*T) := by linarith
    _ = V*m/5000 := he
    _  ≤  E := hE

theorem competition_replenishment (V E final input output : ℝ)
    (hbalance : final+output=V+input) (hfinal : (9/10)*V ≤ final) (hout : E/4 ≤ output) :
    E/4-V/10 ≤ input := by linarith

theorem competition_timed_expected_guarantee (V : ℕ) (s : ℝ≥0) (m : ℕ)
    (p : CompetitionRateBox) (hV : 0 < (V:ℝ)) :
    (V:ℝ)*(m:ℝ)/5000*(1-competitionTimedRootError V s m)  ≤ 
      competitionTimedFullExpectation V s m p hV
        (fun X => (V:ℝ)*(m:ℝ)/5000*FiniteKernel.eventIndicator {Z | competitionTimedFullGood V s m Z} X) := by
  have hh := mul_le_mul_of_nonneg_left (competition_timed_supplied_probability V s m p hV)
    (show 0 ≤ (V:ℝ)*(m:ℝ)/5000 by positivity)
  unfold competitionTimedFullExpectation
  rw [competition_joint_law_scale]
  exact hh

end
end RandomViability.Binding
