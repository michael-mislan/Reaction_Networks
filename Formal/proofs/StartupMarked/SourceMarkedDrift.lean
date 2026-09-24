import proofs.StartupMarked.SourceLogDrift
import proofs.StartupMarked.FoodTaylor

namespace StartupMarked
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

theorem source_retained_reward_drift {n : ℕ} (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hM : (countMass N : ℝ) ≤ 11*V)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ cfg (reactionProduct r)) (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (hK : 4 ≤ N (reactionProduct r)) :
    2-468*(1/500000000 : ℝ)-624*nonfoodMass (fun z => (N z : ℝ)/V)-
      (6146/(N (reactionProduct r) : ℝ)+3072000/(V : ℝ)) ≤
      ∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*retainedReward V r N ch := by
  let U : ℝ := (N (reactionLeft r) : ℝ)/V
  let W : ℝ := (N (reactionRight r) : ℝ)/V
  let C : ℝ := 4*(1/500000000 : ℝ)+(16/3)*nonfoodMass (fun z => (N z : ℝ)/V)
  let du := physicalCoordinateDrift cfg V basal cat N (reactionLeft r)
  let dw := physicalCoordinateDrift cfg V basal cat N (reactionRight r)
  have hnfm : 0 ≤ nonfoodMass (fun z => (N z : ℝ)/V) := by
    apply Finset.sum_nonneg
    intro z _
    split_ifs <;> positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hu := physical_food_drift_bound cfg V hV basal cat N (1/500000000) (by norm_num)
    hb hc hfood hM (reactionLeft r) hl
  have hw := physical_food_drift_bound cfg V hV basal cat N (1/500000000) (by norm_num)
    hb hc hfood hM (reactionRight r) hr
  have hdu := deficit_drift U du C hC hu
  have hdw := deficit_drift W dw C hC hw
  have hprod := food_product_deficit U W (by dsimp [U]; positivity) (by dsimp [W]; positivity)
  have hlog := source_retained_log_drift cfg V hV basal cat N r hb hc hfood hM hl hr hlen
    huw huz hwz hsel hcat hK
  have hpen := food_penalty_generator hn cfg V hV basal cat N r
    (fun rr => (hb rr).trans (by norm_num)) hc hM
  have he : (∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*retainedReward V r N ch) =
      (∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*retainedLog r N ch)+
      ∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*
        (-(foodPenalty V r (unboundedPhysicalNext N ch)-foodPenalty V r N)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ch _
    unfold retainedReward
    ring
  rw [he]
  dsimp [U,W,C,du,dw] at hdu hdw hprod
  linarith only [hdu,hdw,hprod,hlog,hpen]

end
end StartupMarked
