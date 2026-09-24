import proofs.StartupCount.CountFlux

namespace StartupCount
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 40000

theorem double_loss_crossing_boundary (K L h : ℕ) (hdown : K ≤ L+2)
    (hstart : h ≤ K) (hend : L < h) : K = h ∨ K = h+1 := by omega

theorem crossing_rate_le {J : Type*} [Fintype J] (rate : J → ℝ)
    (hr : ∀ j,0 ≤ rate j) (next : J → ℕ) (K h : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hdown : ∀ j,K ≤ next j+2)
    (hflux : (∑ j,rate j*max 0 ((K : ℝ)-next j)) ≤ δ*K) :
    (∑ j,rate j*(if h ≤ K ∧ next j < h then 1 else 0)) ≤
      δ*(h+1 : ℕ)*(if K ≤ h+1 then 1 else 0) := by
  by_cases hb : K ≤ h+1
  · rw [if_pos hb,mul_one]
    have hp (j : J) : rate j*(if h ≤ K ∧ next j < h then 1 else 0) ≤
        rate j*max 0 ((K : ℝ)-next j) := by
      split_ifs with hj
      · have hh : (next j : ℝ)+1 ≤ K := by exact_mod_cast (show next j+1 ≤ K by omega)
        apply mul_le_mul_of_nonneg_left _ (hr j)
        exact le_trans (by linarith : (1 : ℝ) ≤ (K : ℝ)-next j) (le_max_right _ _)
      · simp only [mul_zero]
        exact mul_nonneg (hr j) (le_max_left _ _)
    have hs := (Finset.sum_le_sum (fun j _ => hp j)).trans hflux
    have hk : (K : ℝ) ≤ (h+1 : ℕ) := by exact_mod_cast hb
    exact hs.trans (mul_le_mul_of_nonneg_left hk hδ)
  · rw [if_neg hb,mul_zero]
    have he (j : J) : ¬(h ≤ K ∧ next j < h) := by
      intro hj
      have hh := double_loss_crossing_boundary K (next j) h (hdown j) hj.1 hj.2
      omega
    simp only [if_neg (he _),mul_zero,Finset.sum_const_zero,le_refl]

theorem physical_crossing_rate_le {n : ℕ} (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hM : (countMass N : ℝ) ≤ 11*V) (q : Molecule n) (hlen : molLength q = 4) (h : ℕ) :
    (∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch *
      (if h ≤ N q ∧ unboundedPhysicalNext N ch q < h then 1 else 0)) ≤
      1476*(h+1 : ℕ)*(if N q ≤ h+1 then 1 else 0) := by
  apply crossing_rate_le _ (unboundedPhysicalRate_nonneg cfg V 1 basal cat N)
    (fun ch => unboundedPhysicalNext N ch q) (N q) h 1476 (by norm_num)
  · intro ch
    have hh := physical_downward_jump_le_two N q ch
    have hh' : (N q : ℝ) ≤ (unboundedPhysicalNext N ch q : ℝ)+2 := by linarith
    exact_mod_cast hh'
  · exact adverse_copy_flux_bound cfg V hV basal cat N hb hc hfood hM q hlen

theorem low_after_start_requires_crossing (K : ℕ → ℕ) (J length h : ℕ)
    (hstart : h ≤ K J) (hend : K (J+length) < h) :
    ∃ i < length,h ≤ K (J+i) ∧ K (J+i+1) < h := by
  induction length with
  | zero => simp only [Nat.add_zero] at hend; omega
  | succ length ih =>
    by_cases hm : h ≤ K (J+length)
    · exact ⟨length,by omega,hm,by simpa [Nat.add_assoc] using hend⟩
    · obtain ⟨i,hi,hbefore,hafter⟩ := ih (by omega)
      exact ⟨i,by omega,hbefore,hafter⟩

end
end StartupCount
