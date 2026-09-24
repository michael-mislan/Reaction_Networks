import proofs.SerialTransferSelection.CompactWitness
import Mathlib.Analysis.Complex.ExponentialBounds

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem fraction_from_log_odds (H L : ℝ) (hH : 0 < H) (hL : 0 < L)
    (f : ℝ) (hf : 0 < f) (hf1 : f < 1)
    (hg : Real.log (f/(1-f)) < Real.log H-Real.log L) : f < H/(H+L) := by
  rw [← Real.log_div (ne_of_gt hH) (ne_of_gt hL)] at hg
  have hi := (Real.log_lt_log_iff (by positivity : 0 < f/(1-f)) (div_pos hH hL)).mp hg
  apply (lt_div_iff₀ (add_pos hH hL)).mpr
  have hh := (div_lt_div_iff₀ (show 0 < 1-f by linarith) hL).mp hi
  nlinarith

theorem inverse_target_fraction (H L g : ℝ) (K : ℕ) (hH : 0 < H) (hL : 0 < L)
    (f : ℝ) (hf : 0 < f) (hf1 : f < 1)
    (hdesign : Real.log (2*f/(1-f)) ≤ (K : ℝ)*g)
    (hgain : (K : ℝ)*g-Real.log 2 < Real.log H-Real.log L) : f < H/(H+L) := by
  apply fraction_from_log_odds H L hH hL f hf hf1
  have hid : Real.log (2*f/(1-f))=Real.log 2+Real.log (f/(1-f)) := by
    rw [show 2*f/(1-f)=2*(f/(1-f)) by ring,Real.log_mul (by norm_num) (ne_of_gt (by positivity : 0 < f/(1-f)))]
  rw [hid] at hdesign
  linarith

theorem tenCycle_exponential_gain :
    (93876/100 : ℝ) < Real.exp (10*cycleSizeGain (1/50)-Real.log 2) := by
  have he := Real.exp_bound (x := (-19/50 : ℝ)) (by norm_num) (n := 10) (by norm_num)
  have hl := (abs_le.mp he).1
  norm_num [Finset.sum_range_succ,Nat.factorial] at hl
  have h4 : Real.log (4 : ℝ)=2*Real.log 2 := by
    simpa only [show (2 : ℝ)^2=4 by norm_num,Nat.cast_ofNat] using (Real.log_pow (2 : ℝ) 2)
  have hid : 10*cycleSizeGain (1/50)-Real.log 2 =
      11*Real.log 2+(-19/50)-10*Real.log (51/49) := by
    unfold cycleSizeGain
    norm_num only [show ((1+1/50)/(1-1/50) : ℝ)=51/49 by norm_num]
    rw [h4]
    ring
  rw [hid,Real.exp_sub,Real.exp_add,show (11 : ℝ)=((11 : ℕ) : ℝ) from rfl,
    Real.exp_nat_mul,show (10 : ℝ)=((10 : ℕ) : ℝ) from rfl,Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2),Real.exp_log (by norm_num : (0 : ℝ) < 51/49)]
  norm_num
  linarith

theorem tenCycle_high_fraction (H L : ℝ) (hH : 0 < H) (hL : 0 < L)
    (hg : 10*cycleSizeGain (1/50)-Real.log 2 < Real.log H-Real.log L) :
    (998935/1000000 : ℝ) < H/(H+L) := by
  have he := Real.exp_lt_exp.mpr hg
  rw [← Real.log_div (ne_of_gt hH) (ne_of_gt hL),Real.exp_log (div_pos hH hL)] at he
  have ho := tenCycle_exponential_gain.trans he
  have hh := (lt_div_iff₀ hL).mp ho
  apply (lt_div_iff₀ (add_pos hH hL)).mpr
  nlinarith

theorem compact_minority_integer (C : ℕ)
    (hfloor : (1/4 : ℝ)*(49/204)^10 ≤ (C : ℝ)/(compactM : ℝ)) :
    1598083 ≤ C := by
  norm_num [compactM] at hfloor
  have hc : (1598082 : ℝ) < C := by linarith
  exact_mod_cast hc

theorem cycle_gain_three_quarters : (3/4 : ℝ) < cycleSizeGain (1/50) := by
  have h2 := Real.log_two_gt_d9
  have hratio := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 51/49)
  have h4 : Real.log (4 : ℝ)=2*Real.log 2 := by
    simpa only [show (2 : ℝ)^2=4 by norm_num,Nat.cast_ofNat] using (Real.log_pow (2 : ℝ) 2)
  unfold cycleSizeGain
  norm_num only [show ((1+1/50)/(1-1/50) : ℝ)=51/49 by norm_num]
  rw [h4]
  linarith

theorem target_gain_table :
    Real.log (18 : ℝ) ≤ 4*cycleSizeGain (1/50) ∧
    Real.log (38 : ℝ) ≤ 5*cycleSizeGain (1/50) ∧
    Real.log (198 : ℝ) ≤ 8*cycleSizeGain (1/50) ∧
    Real.log (1998 : ℝ) ≤ 11*cycleSizeGain (1/50) := by
  have h (k a : ℝ) (ha : 0 < a) (hk : 0 < k)
      (he : a < Real.exp (k*(3/4))) : Real.log a ≤ k*cycleSizeGain (1/50) := by
    have hl := Real.log_lt_log ha he
    rw [Real.log_exp] at hl
    have hg := mul_lt_mul_of_pos_left cycle_gain_three_quarters hk
    linarith
  refine ⟨h 4 18 (by norm_num) (by norm_num) ?_,
    h 5 38 (by norm_num) (by norm_num) ?_,
    h 8 198 (by norm_num) (by norm_num) ?_,
    h 11 1998 (by norm_num) (by norm_num) ?_⟩
  · have he := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num) 20
    norm_num [Finset.sum_range_succ,Nat.factorial] at he ⊢
    linarith
  · have he := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 15/4 by norm_num) 20
    norm_num [Finset.sum_range_succ,Nat.factorial] at he ⊢
    linarith
  · have he := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 6 by norm_num) 20
    norm_num [Finset.sum_range_succ,Nat.factorial] at he ⊢
    linarith
  · have he := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 33/4 by norm_num) 20
    norm_num [Finset.sum_range_succ,Nat.factorial] at he ⊢
    linarith

theorem share_history_floor (N M K j : ℕ) (zL zH : ℝ)
    (s : ReadyPopulation N M zL zH)
    (h : Fin K → Option (ReadyPopulation N M zL zH))
    (hh : historyGood (shareHistoryStep N M zL zH shareFloor (1/50)) K j (some s) h)
    (i : Fin K) :
    ∃ y : ReadyPopulation N M zL zH, h i=some y ∧
      ∀ b, shareFloor (j+i.val+1) ≤ ancestralShare b y.val := by
  induction K generalizing j s with
  | zero => exact Fin.elim0 i
  | succ K ih =>
    obtain ⟨hfirst,htail⟩ := hh
    cases he : h 0 with
    | none => simp [he,shareHistoryStep] at hfirst
    | some y =>
      have hy : shareCycleReadyRelation N M zL zH s.val (shareFloor j) (1/50) y := by
        simpa [he,shareHistoryStep] using hfirst
      have htail' : historyGood (shareHistoryStep N M zL zH shareFloor (1/50)) K (j+1)
          (some y) (Fin.tail h) := by simpa [he] using htail
      refine Fin.cases ?_ (fun r => ?_) i
      · refine ⟨y,he,?_⟩
        simpa only [Fin.val_zero,Nat.add_zero,shareFloor_next] using hy.1
      · obtain ⟨z,hz,hfloor⟩ := ih (j+1) y (Fin.tail h) htail' r
        refine ⟨z,hz,?_⟩
        simpa [Fin.val_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hfloor

theorem share_history_count_floor (N M K : ℕ) (hN : 0 < N) (hM : 0 < M) (zL zH : ℝ)
    (s : ReadyPopulation N M zL zH)
    (h : Fin K → Option (ReadyPopulation N M zL zH))
    (hh : historyGood (shareHistoryStep N M zL zH shareFloor (1/50)) K 0 (some s) h)
    (i : Fin K) :
    ∃ y : ReadyPopulation N M zL zH, h i=some y ∧
      ∀ b, (1/4 : ℝ)*(49/204)^(i.val+1) ≤ (ancestralCount b y.val.live : ℝ)/(M : ℝ) := by
  obtain ⟨y,hy,hfloor⟩ := share_history_floor N M K 0 zL zH s h hh i
  refine ⟨y,hy,?_⟩
  intro b
  have hp := (div_le_div_of_nonneg_right (hfloor b) (by norm_num : (0 : ℝ) ≤ 2)).trans
    (ready_share_count N M hN hM zL zH y b)
  dsimp [shareFloor] at hp
  convert hp using 1
  simp only [Nat.zero_add]
  ring

end SerialTransferSelection
