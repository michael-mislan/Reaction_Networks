import proofs.StartupCount.CountFlux
import proofs.StartupCount.DoubleLossTilt
import proofs.RandomViability.PhysicalSelectedFlux

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

/-- Actual basal immigration under the food guard, with unrestricted background. -/
theorem guarded_basal_immigration {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (eps ell : ℝ) (heps : 0 ≤ eps) (hell : 0 ≤ ell)
    (hb : eps ≤ basal r)
    (hu : ell*V ≤ (N (reactionLeft r) : ℝ))
    (hw : ell*V ≤ (N (reactionRight r) : ℝ)) :
    eps*ell^2*V ≤ unboundedPhysicalRate c V 1 basal cat N (.inr (.inl (r,true))) := by
  have hp := mul_le_mul hu hw (mul_nonneg hell hV.le) (by positivity)
  have he := mul_le_mul_of_nonneg_left hp heps
  have hb' := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (N (reactionLeft r) : ℝ)*N (reactionRight r) by positivity)
  have hd := (div_le_div_of_nonneg_right (he.trans hb') hV.le).trans
    (basal_distinct_monomial_lower c V hV basal cat N r huw)
  have hEq : eps*(ell*V*(ell*V))/(V : ℝ) = eps*ell^2*V := by
    field_simp
  rwa [hEq] at hd

theorem basal_product_next {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hu : 1 ≤ N (reactionLeft r)) (hw : 1 ≤ N (reactionRight r)) :
    unboundedPhysicalNext N (.inr (.inl (r,true))) (reactionProduct r) =
      N (reactionProduct r)+1 := by
  have hen : ∀ y,physicalChannelInput (.inr (.inl (r,true))) y ≤ N y := by
    intro y
    by_cases hyu : y = reactionLeft r
    · subst y; simpa [physicalChannelInput,singleCount,huw] using hu
    · by_cases hyw : y = reactionRight r
      · subst y; simpa [physicalChannelInput,singleCount,Ne.symm huw] using hw
      · simp [physicalChannelInput,singleCount,hyu,hyw]
  rw [unboundedPhysicalNext,if_pos hen]
  simp [applyCountChannel,physicalChannelInput,
    physicalChannelOutput,singleCount,Ne.symm huz,Ne.symm hwz]

/-- The count tilt is evaluated against every actual physical channel. The
food and mass guards are explicit; no comparison process is substituted. -/
theorem physical_guarded_count_tilt {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → c z = ∅)
    (hM : (countMass N : ℝ) ≤ 11*V) (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hbas : (1/500000000 : ℝ) ≤ basal r)
    (ell : ℝ) (hell : 0 < ell)
    (hu : ell*V ≤ (N (reactionLeft r) : ℝ))
    (hw : ell*V ≤ (N (reactionRight r) : ℝ)) (s : ℝ) (hs : 0 ≤ s) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch *
      (Real.exp (s*((N (reactionProduct r) : ℝ)-
        unboundedPhysicalNext N ch (reactionProduct r)))-1)) ≤
    -(1/500000000 : ℝ)*ell^2*V*(1-Real.exp (-s)) +
      1476/2*(Real.exp (2*s)-1)*N (reactionProduct r) := by
  have hu' : 1 ≤ N (reactionLeft r) := by
    have hh : (0 : ℝ) < N (reactionLeft r) := (mul_pos hell hV).trans_le hu
    exact Nat.one_le_iff_ne_zero.mpr (by intro h; simp [h] at hh)
  have hw' : 1 ≤ N (reactionRight r) := by
    have hh : (0 : ℝ) < N (reactionRight r) := (mul_pos hell hV).trans_le hw
    exact Nat.one_le_iff_ne_zero.mpr (by intro h; simp [h] at hh)
  have hd (ch : PhysicalCountChannel n) : N (reactionProduct r) ≤
      unboundedPhysicalNext N ch (reactionProduct r)+2 := by
    have hh := physical_downward_jump_le_two N (reactionProduct r) ch
    have hh' : (N (reactionProduct r) : ℝ) ≤
        (unboundedPhysicalNext N ch (reactionProduct r) : ℝ)+2 := by linarith
    exact_mod_cast hh'
  have hh := StartupCount.immigration_double_loss_generator
    (unboundedPhysicalRate c V 1 basal cat N)
    (unboundedPhysicalRate_nonneg c V 1 basal cat N)
    (fun ch => unboundedPhysicalNext N ch (reactionProduct r)) (N (reactionProduct r))
    (.inr (.inl (r,true))) (basal_product_next N r huw huz hwz hu' hw')
    ((1/500000000 : ℝ)*ell^2*V) 1476 s hs
    (guarded_basal_immigration c V hV basal cat N r huw _ ell (by norm_num)
      hell.le hbas hu hw) hd
    (adverse_copy_flux_bound c V hV basal cat N hb hc hfood hM _ hlen)
  simpa only [neg_mul] using hh

end
end RandomViability
