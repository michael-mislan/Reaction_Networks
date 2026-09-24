import proofs.StartupCount.PhysicalTilt
import proofs.StartupCount.AffineCountTilt

namespace StartupCount
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 60000

theorem exp_count_shift (s : ℝ) (K L : ℕ) :
    Real.exp (-s*(K : ℝ))*(Real.exp (s*((K : ℝ)-L))-1) =
      Real.exp (-s*(L : ℝ))-Real.exp (-s*(K : ℝ)) := by
  rw [mul_sub,mul_one,← Real.exp_add]
  congr 2
  ring

theorem exp_log_count (K : ℕ) :
    Real.exp (-Real.log (10/9)*(K : ℝ)) = (9/10 : ℝ)^K := by
  rw [mul_comm,Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 10/9)]
  congr 1
  norm_num

/-- Actual finite-count generator of the stationary power tilt. -/
theorem physical_power_generator {n : ℕ} (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hM : (countMass N : ℝ) ≤ 11*V) (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hbas : (1/500000000 : ℝ) ≤ basal r)
    (ell : ℝ) (hell : 0 < ell)
    (hu : ell*V ≤ (N (reactionLeft r) : ℝ))
    (hw : ell*V ≤ (N (reactionRight r) : ℝ)) :
    (∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch *
      ((9/10 : ℝ)^(unboundedPhysicalNext N ch (reactionProduct r))-
        (9/10 : ℝ)^(N (reactionProduct r)))) ≤
    (-(1/500000000 : ℝ)*ell^2*V/10+(1558/9)*(N (reactionProduct r) : ℝ))*
      (9/10 : ℝ)^(N (reactionProduct r)) := by
  let s : ℝ := Real.log (10/9)
  have hs : 0 ≤ s := Real.log_nonneg (by norm_num)
  have he₁ : Real.exp (-s) = (9/10 : ℝ) := by
    dsimp [s]
    rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 10/9)]
    norm_num
  have he₂ : Real.exp (2*s) = (100/81 : ℝ) := by
    rw [two_mul,Real.exp_add]
    dsimp [s]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 10/9)]
    norm_num
  have hh := mul_le_mul_of_nonneg_left
    (physical_guarded_count_tilt cfg V hV basal cat N r hb hc hfood hM hlen huw huz hwz
      hbas ell hell hu hw s hs) (Real.exp_pos (-s*(N (reactionProduct r) : ℝ))).le
  rw [Finset.mul_sum] at hh
  have he (ch : PhysicalCountChannel n) :
      Real.exp (-s*(N (reactionProduct r) : ℝ)) *
        (unboundedPhysicalRate cfg V 1 basal cat N ch *
          (Real.exp (s*((N (reactionProduct r) : ℝ)-unboundedPhysicalNext N ch (reactionProduct r)))-1)) =
      unboundedPhysicalRate cfg V 1 basal cat N ch *
        ((9/10 : ℝ)^(unboundedPhysicalNext N ch (reactionProduct r))-(9/10 : ℝ)^(N (reactionProduct r))) := by
    rw [mul_left_comm,exp_count_shift,exp_log_count,exp_log_count]
  simp_rw [he] at hh
  rw [he₁,he₂,exp_log_count] at hh
  convert hh using 1
  ring

def foodFloor : ℝ := 1/1358-1/50000

theorem foodFloor_pos : 0 < foodFloor := by norm_num [foodFloor]

theorem source_affine_margin (V : ℝ) (hV : 0 ≤ V) (m : ℕ)
    (hm : (m : ℝ) ≤ V/2000000000000000000) :
    V/100000000000000000+(1558/9)*(m : ℝ) ≤ (1/500000000)*foodFloor^2*V/10 := by
  norm_num [foodFloor] at *
  linarith

theorem physical_power_affine_generator {n : ℕ} (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hM : (countMass N : ℝ) ≤ 11*V) (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hbas : (1/500000000 : ℝ) ≤ basal r)
    (hu : foodFloor*V ≤ (N (reactionLeft r) : ℝ))
    (hw : foodFloor*V ≤ (N (reactionRight r) : ℝ))
    (m : ℕ) (hm : 10 ≤ m) (hmV : (m : ℝ) ≤ (V : ℝ)/2000000000000000000) :
    (∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch *
      ((9/10 : ℝ)^(unboundedPhysicalNext N ch (reactionProduct r))-
        (9/10 : ℝ)^(N (reactionProduct r)))) ≤
    -((V : ℝ)/100000000000000000)*(9/10 : ℝ)^(N (reactionProduct r))+
      (1558/9)*(m : ℝ)*(9/10 : ℝ)^m := by
  have hh := physical_power_generator cfg V hV basal cat N r hb hc hfood hM hlen
    huw huz hwz hbas foodFloor foodFloor_pos hu hw
  have he := affine_power_envelope m (N (reactionProduct r)) hm
    ((1/500000000)*foodFloor^2*V/10) (1558/9) ((V : ℝ)/100000000000000000)
    (by norm_num) (source_affine_margin V hV.le m hmV)
  apply hh.trans
  convert he using 1
  ring

theorem source_clock_dominates {n : ℕ} (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    (V : ℝ)/100000000000000000 < ∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch := by
  have hcard : Fintype.card ↥(binaryFood n 2) = 6 :=
    (Fintype.card_congr (foodWordEquiv hn)).trans (by decide)
  obtain ⟨f⟩ : Nonempty ↥(binaryFood n 2) := Fintype.card_pos_iff.mp (by rw [hcard]; norm_num)
  have hh := Finset.single_le_sum (f := unboundedPhysicalRate cfg V 1 basal cat N)
    (fun ch _ => unboundedPhysicalRate_nonneg cfg V 1 basal cat N ch)
    (Finset.mem_univ (.inl (.inl f)))
  rw [unbounded_feed_rate] at hh
  norm_num only [NNReal.coe_one,one_mul] at hh
  linarith

end
end StartupCount
