import proofs.RandomViability.CensoredNonfoodMaximal

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def collectiveNoiseTheta (n V δ T : ℝ) : ℝ := δ*V/(2*n*(96011*T+δ))

theorem collective_noise_scale (n V δ T : ℝ) (hn : 4 ≤ n) (hV : 0 < V)
    (hδ : 0 < δ) (hT : 0 ≤ T) :
    0 ≤ collectiveNoiseTheta n V δ T ∧
    |collectiveNoiseTheta n V δ T| *(n/V) ≤ 1 ∧
    -collectiveNoiseTheta n V δ T*δ+(collectiveNoiseTheta n V δ T)^2*((384000+11*n)/V)*T ≤
      -(δ^2*V/(4*n*(96011*T+δ))) := by
  let A := 96011*T+δ
  let θ := collectiveNoiseTheta n V δ T
  have hn0 : 0 < n := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hθ : 0 ≤ θ := by dsimp [θ,collectiveNoiseTheta]; positivity
  have ht : |θ| *(n/V) ≤ 1 := by
    rw [abs_of_nonneg hθ]
    have he : θ*(n/V) = δ/(2*A) := by
      dsimp [θ,collectiveNoiseTheta,A]
      field_simp
    rw [he]
    apply (div_le_one (by positivity : 0 < 2*A)).mpr
    dsimp [A]
    linarith
  have hq : (384000+11*n)/V ≤ 96011*n/V := by
    apply div_le_div_of_nonneg_right _ hV.le
    linarith
  have hratio : 96011*T/A ≤ 1 := (div_le_one hA).mpr (by dsimp [A]; linarith)
  have hcost : θ^2*((384000+11*n)/V)*T ≤ θ*δ/2 := by
    calc
      _ ≤ θ^2*(96011*n/V)*T := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hq (sq_nonneg θ)) hT
      _ = (θ*δ/2)*(96011*T/A) := by
        dsimp [θ,collectiveNoiseTheta,A]
        field_simp
      _ ≤ (θ*δ/2)*1 := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := mul_one _
  refine ⟨hθ,ht,?_⟩
  calc
    _ ≤ -θ*δ/2 := by linarith
    _ = _ := by
      dsimp [θ,collectiveNoiseTheta]
      field_simp
      ring

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- An explicit uniform exp(-c V/n) bound for the censored nonfood compensation.
The coefficient c depends on δ and T, not the host or catalog horizon n. -/
theorem physical_censored_nonfood_volume_rate (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      (⋃ K,{z | censoredNonfoodFluctuationBy c V basal cat T stop δ K z}) ≤
      ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δ))))) := by
  have hs := collective_noise_scale (n : ℝ) V δ T (by exact_mod_cast hn) hV hδ hT
  exact (physical_censored_nonfood_any_index_tail hn c V hV basal cat N hbasal hcat
    (collectiveNoiseTheta n V δ T) T hs.1 hs.2.1 hT stop hstop δ).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hs.2.2))

end
end RandomViability
