import proofs.RandomViability.ProductivePathRates
import proofs.RandomViability.ProductiveCylinder
import proofs.RandomViability.PhysicalTrajectory

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

def productivePaidState {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (f : ↥(binaryFood n 2)) (m i : ℕ) : Molecule n → ℕ :=
  if i ≤ 3*m then productivePathState N r m i else
    unboundedPhysicalNext (productivePathState N r m (3*m)) (.inl (.inl f))

def productivePaidLabel {n : ℕ} (r : Reaction n) (f : ↥(binaryFood n 2))
    (m i : ℕ) : PhysicalCountChannel n :=
  if i < 3*m then productivePathLabel r m i else .inl (.inl f)

theorem productive_paid_initial {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (hp : N (reactionProduct r)=0) (f : ↥(binaryFood n 2)) (m : ℕ) :
    productivePaidState N r f m 0 = N := by
  rw [productivePaidState, if_pos (Nat.zero_le _), productive_path_initial N r hp]

theorem productive_paid_next {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (f : ↥(binaryFood n 2)) (m : ℕ) (hm : 0 < m)
    (hu : 2*m < N (reactionLeft r)) (hw : 2*m < N (reactionRight r))
    (i : ℕ) (hi : i < 3*m+1) :
    unboundedPhysicalNext (productivePaidState N r f m i) (productivePaidLabel r f m i) =
      productivePaidState N r f m (i+1) := by
  by_cases hk : i < 3*m
  · simp only [productivePaidState, productivePaidLabel, if_pos hk,
      if_pos hk.le, if_pos (show i+1 ≤ 3*m by omega)]
    exact productive_path_next N r huw hup hwp m hm hu hw i hk
  · have he : i=3*m := by omega
    subst i
    simp [productivePaidState, productivePaidLabel]

variable {n : ℕ} [mCh : MeasurableSpace (PhysicalCountChannel n)]
  [sCh : MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Quantitative probability of the explicit physical productive sequence,
including a paid terminal feed window. No path-transition or rate hypotheses
remain abstract: they follow from the literal count/resource assumptions. -/
theorem physical_productive_cylinder_lower (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (hp : N (reactionProduct r)=0) (f : ↥(binaryFood n 2))
    (V m : ℕ) (hV : 1 ≤ V) (hm : 0 < m) (hmV : 4*m ≤ V)
    (hu : N (reactionLeft r)=V) (hw : N (reactionRight r)=V) (hM : countMass N ≤ 10*V)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (eps : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hb : eps ≤ (basal r : ℝ))
    (hc : 4 ≤ (cat r (reactionProduct r) : ℝ)) (hsel : r ∈ c (reactionProduct r))
    (hbasal : ∀ r, (basal r : ℝ) ≤ 1) (hcat : ∀ r z, (cat r z : ℝ) ≤ 16)
    (a d : ℕ → ℝ) (ha : ∀ i < 3*m+1, 0 ≤ a i) (hd : ∀ i < 3*m+1, 0 ≤ d i) :
    (∏ i : Fin (3*m+1), ENNReal.ofReal (eps*d i*Real.exp (-(24000*(V : ℝ))*(a i+d i)))) ≤
      physicalTrajectoryLaw hn c (V : NNReal) 1
        (by exact_mod_cast (show 0 < V by omega)) (by norm_num) basal cat N
        (prescribedCylinder (productivePaidState N r f m) (productivePaidLabel r f m) a d (3*m+1)) := by
  have hVpos : 0 < ((V : NNReal) : ℝ) := by
    change 0 < (V : ℝ)
    exact_mod_cast (show 0 < V by omega)
  have hDpos : 0 < ((1 : NNReal) : ℝ) := by norm_num
  have hstep : ∀ i < 3*m+1, unboundedPhysicalNext (productivePaidState N r f m i)
      (productivePaidLabel r f m i) = productivePaidState N r f m (i+1) := by
    intro i hi
    exact productive_paid_next N r huw hup hwp f m hm (by omega) (by omega) i hi
  have hQ : ∀ i < 3*m+1,
      (∑ ch, unboundedPhysicalRate c (V : NNReal) 1 basal cat (productivePaidState N r f m i) ch) ≤
        24000*(V : ℝ) := by
    intro i hi
    rw [productivePaidState, if_pos (show i ≤ 3*m by omega)]
    exact productive_path_total_rate_bound hn c N r huw hup hwp hp V m hV hmV hu hw hM basal cat hbasal hcat i (by omega)
  have he : ∀ i < 3*m+1, eps ≤ unboundedPhysicalRate c (V : NNReal) 1 basal cat
      (productivePaidState N r f m i) (productivePaidLabel r f m i) := by
    intro i hi
    rw [productivePaidState, if_pos (show i ≤ 3*m by omega)]
    unfold productivePaidLabel
    by_cases hk : i < 3*m
    · rw [if_pos hk]
      exact productive_path_rate_lower c N r huw hup hwp hp V m hV hm hmV hu hw basal cat eps heps1 hb hc hsel i hk
    · rw [if_neg hk, unbounded_feed_rate]
      have hv : (1 : ℝ) ≤ V := by exact_mod_cast hV
      simpa only [NNReal.coe_one, one_mul, NNReal.coe_natCast] using heps1.trans hv
  have hout := prescribed_cylinder_probability_lower unboundedPhysicalNext
    (unboundedPhysicalRate c (V : NNReal) 1 basal cat)
    (unboundedPhysicalRate_nonneg c (V : NNReal) 1 basal cat)
    (unbounded_total_pos hn c (V : NNReal) 1 hVpos hDpos basal cat)
    (productivePaidState N r f m) (productivePaidLabel r f m) a d
    (fun _ => 24000*(V : ℝ)) (fun _ => eps) (3*m+1) hstep hQ ha hd (fun _ _ => heps) he
  rw [productive_paid_initial N r hp] at hout
  exact hout

end
end RandomViability
