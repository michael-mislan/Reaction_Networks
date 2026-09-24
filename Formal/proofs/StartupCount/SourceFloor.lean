import proofs.StartupCount.SourceCrossing
import proofs.StartupCount.SourceTail
import proofs.StartupCount.DyadicCertificate

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000

theorem fixed_window_integral (A : ℝ≥0∞) :
    (∫⁻ t : ℝ,if (1 : ℝ) < t ∧ t ≤ 199 then A else 0) = A*198 := by
  have he : (fun t : ℝ => if (1 : ℝ) < t ∧ t ≤ 199 then A else 0) =
      (Ioc (1 : ℝ) 199).indicator (fun _ => A) := by
    funext t
    simp only [Set.indicator,Set.mem_Ioc]
  rw [he]
  rw [lintegral_indicator measurableSet_Ioc,lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc]
  norm_num

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem source_count_floor_coarse (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hbas : (1/500000000 : ℝ) ≤ basal r)
    (m : ℕ) (hm : 10 ≤ m) (hmV : (m : ℝ) ≤ (V : ℝ)/2000000000000000000)
    (N₀ : Molecule n → ℕ) (h : ℕ) (hh : 0 < h) (hhm : h+1 ≤ m) :
    physicalTrajectoryLaw hn cfg V 1 hV (by norm_num) basal cat N₀
      (lowDuring (countGuard V r) (fun N => N (reactionProduct r)) h 1 199) ≤
      ENNReal.ofReal (10*(1+1476*(h+1 : ℕ)*198)*(9/10 : ℝ)^(m-h-1)) := by
  let μ := physicalTrajectoryLaw hn cfg V 1 hV (by norm_num) basal cat N₀
  let A := ENNReal.ofReal (10*(9/10 : ℝ)^(m-h-1))
  have htail (l : ℕ) (hl : l ≤ h+1) (t : ℝ) (ht : 1 ≤ t) :
      μ (guardedLowEvent (countGuard V r) (fun N => N (reactionProduct r)) l t) ≤ A := by
    apply (source_count_tail hn cfg V hV basal cat r hb hc hfood hlen huw huz hwz hbas
      m hm hmV t ht N₀ l (hl.trans hhm)).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : m-h-1 ≤ m-l)) (by norm_num)
  have hi : (∫⁻ t : ℝ,if (1 : ℝ) < t ∧ t ≤ 199 then ENNReal.ofReal (1476*(h+1 : ℕ))*
      μ (guardedLowEvent (countGuard V r) (fun N => N (reactionProduct r)) (h+1) t) else 0) ≤
      (ENNReal.ofReal (1476*(h+1 : ℕ))*A)*198 := by
    rw [← fixed_window_integral]
    apply lintegral_mono
    intro t
    dsimp only
    split_ifs with ht
    · exact mul_le_mul_right (htail (h+1) le_rfl t ht.1.le) _
    · rfl
  have hhbound := source_count_crossing_bound hn cfg V hV basal cat r hb hc hfood hlen
    N₀ h hh 1 199 (by norm_num)
  have hresult := hhbound.trans (add_le_add (htail (h-1) (by omega) 1 le_rfl) hi)
  apply hresult.trans
  apply le_of_eq
  dsimp [A]
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_ofNat 198,
    ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem source_count_floor_uniform (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 1000000000000000000000000 ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hbas : (1/500000000 : ℝ) ≤ basal r) (N₀ : Molecule n → ℕ) :
    physicalTrajectoryLaw hn cfg V 1 (by linarith) (by norm_num) basal cat N₀
      (lowDuring (countGuard V r) (fun N => N (reactionProduct r)) (stockThreshold V) 1 199) <
      ENNReal.ofReal (1/1000000 : ℝ) := by
  obtain ⟨hm,hmV,hN,hgap,_,_⟩ := count_rounding_bounds V hV
  have hv : 0 < (V : ℝ) := by linarith
  have hh : 0 < stockThreshold V := Nat.ceil_pos.mpr (by positivity)
  have hhm : stockThreshold V+1 ≤ countCut V := by omega
  apply (source_count_floor_coarse hn cfg V hv basal cat r hb hc hfood hlen huw huz hwz hbas
    (countCut V) hm hmV N₀ (stockThreshold V) hh hhm).trans_lt
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
    (uniform_crossing_scalar_certificate V hV)

end
end StartupCount
