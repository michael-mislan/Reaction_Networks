import proofs.RandomViability.ProductivePath

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 40000

theorem productive_path_food_floor {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r) (V m i : ℕ)
    (hu : N (reactionLeft r)=V) (hw : N (reactionRight r)=V)
    (hm : 4*m ≤ V) (hi : i ≤ 3*m) :
    V ≤ 2*productivePathState N r m i (reactionLeft r) ∧
    V ≤ 2*productivePathState N r m i (reactionRight r) := by
  have hb := (productive_schedule_bounds m i hi).2.1
  simp [productivePathState, productiveCounts, hu, Ne.symm huw, hw]
  omega

theorem productive_path_rate_lower {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (hp : N (reactionProduct r)=0) (V m : ℕ) (hV : 1 ≤ V) (hm : 0 < m) (hmV : 4*m ≤ V)
    (hu : N (reactionLeft r)=V) (hw : N (reactionRight r)=V)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (eps : ℝ) (heps1 : eps ≤ 1) (hb : eps ≤ (basal r : ℝ))
    (hc : 4 ≤ (cat r (reactionProduct r) : ℝ)) (hsel : r ∈ c (reactionProduct r))
    (i : ℕ) (hi : i < 3*m) :
    eps ≤ unboundedPhysicalRate c (V : NNReal) 1 basal cat
      (productivePathState N r m i) (productivePathLabel r m i) := by
  have hVpos : 0 < ((V : NNReal) : ℝ) := by
    change 0 < (V : ℝ)
    exact_mod_cast (show 0 < V by omega)
  have hVone : (1 : ℝ) ≤ V := by exact_mod_cast hV
  by_cases hi0 : i=0
  · subst i
    rw [productive_path_initial N r hp]
    simp only [productivePathLabel, ite_true]
    have hh := bounded_basal_ligation_rate_distinct c (V : NNReal) 1 hVpos basal cat
      (countsAtOwnMass N) r huw (by change 1 ≤ N (reactionLeft r); omega)
      (by change 1 ≤ N (reactionRight r); omega)
    change unboundedPhysicalRate c (V : NNReal) 1 basal cat N _ =
      (basal r : ℝ)*((N (reactionLeft r) : ℝ)*N (reactionRight r))/(V : ℝ) at hh
    rw [hh,hu,hw]
    have heq : (basal r : ℝ)*((V : ℝ)*V)/(V : ℝ) = (basal r : ℝ)*V := by field_simp
    rw [heq]
    have hmul := mul_le_mul hb hVone (by norm_num : (0 : ℝ) ≤ 1) (NNReal.coe_nonneg _)
    simpa only [mul_one] using hmul
  · have hpos := productive_schedule_positive m i hm (Nat.pos_of_ne_zero hi0)
    have hz : 1 ≤ productivePathState N r m i (reactionProduct r) := by
      simp [productivePathState, productiveCounts, Ne.symm hup, Ne.symm hwp]
      omega
    unfold productivePathLabel
    rw [if_neg hi0]
    by_cases hs : productiveLigationStep m i
    · rw [if_pos hs]
      have hf := productive_path_food_floor N r huw V m i hu hw hmV hi.le
      have hfu : ((V : NNReal) : ℝ)/2 ≤ productivePathState N r m i (reactionLeft r) := by
        have hh : (V : ℝ) ≤ 2*(productivePathState N r m i (reactionLeft r) : ℝ) := by exact_mod_cast hf.1
        change (V : ℝ)/2 ≤ _
        linarith
      have hfw : ((V : NNReal) : ℝ)/2 ≤ productivePathState N r m i (reactionRight r) := by
        have hh : (V : ℝ) ≤ 2*(productivePathState N r m i (reactionRight r) : ℝ) := by exact_mod_cast hf.2
        change (V : ℝ)/2 ≤ _
        linarith
      exact heps1.trans (productive_catalytic_rate_lower c (V : NNReal) 1 hVpos basal cat
        _ r _ huw hup hwp hfu hfw hz hsel hc)
    · rw [if_neg hs]
      have hh := bounded_outflow_rate c (V : NNReal) 1 hVpos basal cat
        (countsAtOwnMass (productivePathState N r m i)) (reactionProduct r)
      change unboundedPhysicalRate c (V : NNReal) 1 basal cat (productivePathState N r m i) _ =
        (1 : ℝ)*(productivePathState N r m i (reactionProduct r) : ℝ) at hh
      rw [hh,one_mul]
      exact heps1.trans (by exact_mod_cast hz)

theorem productive_path_total_rate_bound {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (hp : N (reactionProduct r)=0) (V m : ℕ) (hV : 1 ≤ V) (hmV : 4*m ≤ V)
    (hu : N (reactionLeft r)=V) (hw : N (reactionRight r)=V) (hM : countMass N ≤ 10*V)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r, (basal r : ℝ) ≤ 1) (hc : ∀ r z, (cat r z : ℝ) ≤ 16)
    (i : ℕ) (hi : i ≤ 3*m) :
    (∑ ch, unboundedPhysicalRate c (V : NNReal) 1 basal cat (productivePathState N r m i) ch) ≤
      24000*(V : ℝ) := by
  have hmass := productive_path_mass_le N r huw hup hwp hp m (by omega) (by omega) i hi
  have hVpos : 0 < ((V : NNReal) : ℝ) := by
    change 0 < (V : ℝ)
    exact_mod_cast (show 0 < V by omega)
  exact unbounded_total_rate_mass_ten hn c (V : NNReal) hVpos basal cat _
    (by exact_mod_cast hmass.trans hM) hb hc

end
end RandomViability
