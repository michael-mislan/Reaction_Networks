import proofs.StartupMarked.RetainedMoments

namespace StartupMarked
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

theorem source_retained_log_drift {n : ℕ} (cfg : SourceMoleculeFibreConfig n)
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
    4*((N (reactionLeft r) : ℝ)/V)*((N (reactionRight r) : ℝ)/V)-1-
      25*(4*(1/500000000 : ℝ)+(16/3)*nonfoodMass (fun z => (N z : ℝ)/V))-
      6146/(N (reactionProduct r) : ℝ) ≤
      ∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*retainedLog r N ch := by
  let K : ℝ := N (reactionProduct r)
  let U : ℝ := (N (reactionLeft r) : ℝ)/V
  let W : ℝ := (N (reactionRight r) : ℝ)/V
  let C : ℝ := 4*(1/500000000 : ℝ)+(16/3)*nonfoodMass (fun z => (N z : ℝ)/V)
  let selectedRate := unboundedPhysicalRate cfg V 1 basal cat N (selectedForward r)
  let A := ∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*retainedChange r N ch
  let B := ∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*(retainedChange r N ch)^2
  have hk : 0 < K := by dsimp [K]; exact_mod_cast (show 0 < N (reactionProduct r) by omega)
  have hselectedRate : 4*K*U*W ≤ selectedRate := by
    have hs := catalytic_distinct_monomial_lower cfg V hV basal cat N r (reactionProduct r)
      huw huz hwz hsel
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcat (show 0 ≤
        (N (reactionLeft r) : ℝ)*N (reactionRight r)*N (reactionProduct r) by positivity)) (sq_nonneg (V : ℝ))
    apply le_trans _ (hh.trans hs)
    apply le_of_eq
    dsimp [K,U,W]
    ring
  have ha := adverse_copy_flux_mass_bound cfg V hV basal cat N (1/500000000) (by norm_num)
    hb hc hfood hM (reactionProduct r) hlen
  have hA : K*(4*U*W-1-25*C) ≤ A := by
    dsimp [A]
    rw [retained_first_moment cfg V basal cat r N huz hwz]
    change adverseCopyFlux cfg V basal cat N (reactionProduct r) ≤ (1+25*C)*K at ha
    change _ ≤ selectedRate-adverseCopyFlux cfg V basal cat N (reactionProduct r)
    nlinarith only [hselectedRate,ha]
  have hb2 := retained_second_moment cfg V basal cat r N huz hwz
  have hselectedRateu := selected_forward_rate_le cfg V hV basal cat N r (hc r _) hM huw hl hr
  have hlu := adverse_copy_flux_bound cfg V hV basal cat N hb hc hfood hM (reactionProduct r) hlen
  have hB : B ≤ 3073*K := by dsimp [B,K]; linarith only [hb2,hselectedRateu,hlu]
  have hAd : 4*U*W-1-25*C ≤ A/K := (le_div_iff₀ hk).mpr (by nlinarith only [hA])
  have hBd := div_le_div_of_nonneg_right hB (sq_nonneg K)
  have he : 2*(3073*K/K^2) = 6146/K := by field_simp; ring
  have hTaylor := physical_retained_log_taylor cfg V basal cat N r hK
  change A/K-2*B/K^2 ≤ _ at hTaylor
  change 4*U*W-1-25*C-6146/K ≤ _
  have hBd2 : 2*B/K^2 ≤ 6146/K := by
    calc
      _ = 2*(B/K^2) := by ring
      _ ≤ 2*(3073*K/K^2) := mul_le_mul_of_nonneg_left hBd (by norm_num)
      _ = _ := he
  exact (sub_le_sub hAd hBd2).trans hTaylor

end
end StartupMarked
