import proofs.RandomViability.NonfoodIntervalControl
import proofs.RandomViability.JumpWaitingSupport

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def signedNonfoodFluctuationBy {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (θ δ : ℝ) (K : ℕ) (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  ∃ j,j ≤ K ∧ δ ≤ θ*(∑ i : Fin j,censoredNonfoodCompensation c V basal cat T stop
    i (Preorder.frestrictLe (i : ℕ) z) (z ((i : ℕ)+1)))

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_signed_nonfood_crossing_tail (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (θ T : ℝ) (hθ : |θ| *((n : ℝ)/V) ≤ 1) (hT : 0 ≤ T)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (δ : ℝ) (K : ℕ) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | signedNonfoodFluctuationBy c V basal cat T stop θ δ K z} ≤
      ENNReal.ofReal (Real.exp (-δ+θ^2*((384000+11*(n : ℝ))/V)*T)) := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
  let κ := jumpHistoryKernel unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
    (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  let m := censoredNonfoodMultiplier c V basal cat θ T stop
  let L := δ-θ^2*((384000+11*(n : ℝ))/V)*T
  let a := ENNReal.ofReal (Real.exp L)
  let B := ENNReal.ofReal (Real.exp (-L))
  let W : Set (ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :=
    {z | ∀ i,0 ≤ (z (i+1)).2.2}
  have hw : ∀ᵐ z ∂μ,z ∈ W := jumpTrajectory_wait_nonneg N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hc := predictable_product_crossing_bound μ κ
    (fun k => physicalTrajectoryLaw_transition (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N k)
    m (censoredNonfoodMultiplier_measurable c V basal cat θ T stop hstop)
    (physical_censored_nonfood_mean hn c V hV basal cat hbasal hcat θ T hθ stop) a K
  have hsub : W ∩ {z | signedNonfoodFluctuationBy c V basal cat T stop θ δ K z} ⊆
      {z | ∃ j,j ≤ K ∧ a ≤ trajectoryProduct m j z} := by
    intro z hz
    obtain ⟨j,hj,hA⟩ := hz.2
    refine ⟨j,hj,?_⟩
    dsimp only [m,a]
    rw [censored_nonfood_product_exp]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have ht := censored_nonfood_time_bound V T hT stop z hz.1 j
    exact sub_le_sub hA
      (mul_le_mul_of_nonneg_left ht (by positivity))
  have heq : μ (W ∩ {z | signedNonfoodFluctuationBy c V basal cat T stop θ δ K z}) =
      μ {z | signedNonfoodFluctuationBy c V basal cat T stop θ δ K z} :=
    Measure.measure_inter_eq_of_ae hw
  have ht : a*μ {z | signedNonfoodFluctuationBy c V basal cat T stop θ δ K z} ≤ 1 := by
    rw [← heq]
    exact (mul_le_mul_right (measure_mono hsub) a).trans hc
  have hinv : B*a = 1 := by
    dsimp [B,a]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,neg_add_cancel,
      Real.exp_zero,ENNReal.ofReal_one]
  have hb : μ {z | signedNonfoodFluctuationBy c V basal cat T stop θ δ K z} ≤ B := by
    calc
      _ = B*(a*μ {z | signedNonfoodFluctuationBy c V basal cat T stop θ δ K z}) := by
        rw [← mul_assoc,hinv,one_mul]
      _ ≤ B*1 := mul_le_mul_right ht B
      _ = _ := mul_one _
  have he : -L = -δ+θ^2*((384000+11*(n : ℝ))/V)*T := by dsimp [L]; ring
  simpa only [B,he] using hb

theorem physical_signed_nonfood_any_index_tail (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (θ T : ℝ) (hθ : |θ| *((n : ℝ)/V) ≤ 1) (hT : 0 ≤ T)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (δ : ℝ) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      (⋃ K,{z | signedNonfoodFluctuationBy c V basal cat T stop θ δ K z}) ≤
      ENNReal.ofReal (Real.exp (-δ+θ^2*((384000+11*(n : ℝ))/V)*T)) := by
  have hm : Monotone (fun K => {z | signedNonfoodFluctuationBy c V basal cat T stop θ δ K z}) := by
    intro K J hK z hz
    obtain ⟨j,hj,hA⟩ := hz
    exact ⟨j,hj.trans hK,hA⟩
  rw [hm.measure_iUnion]
  exact iSup_le (fun K => physical_signed_nonfood_crossing_tail hn c V hV basal cat N
    hbasal hcat θ T hθ hT stop hstop δ K)

/-- Uniform two-sided nonfood compensation bound; no union cost in jump count. -/
theorem physical_nonfood_two_sided_tail (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ∃ K,δ ≤ |censoredNonfoodPrefix c V basal cat T stop z K|} ≤
      2*ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δ))))) := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
  let θ := collectiveNoiseTheta n V δ T
  let E := fun t : ℝ => ⋃ K,{z | signedNonfoodFluctuationBy c V basal cat T stop t (θ*δ) K z}
  let B := ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δ)))))
  have hs := collective_noise_scale (n : ℝ) V δ T (by exact_mod_cast hn) hV hδ hT
  have hp : μ (E θ) ≤ B :=
    (physical_signed_nonfood_any_index_tail hn c V hV basal cat N hbasal hcat θ T
      hs.2.1 hT stop hstop (θ*δ)).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
        simpa only [neg_mul] using hs.2.2)))
  have hm : μ (E (-θ)) ≤ B :=
    (physical_signed_nonfood_any_index_tail hn c V hV basal cat N hbasal hcat (-θ) T
      (by simpa only [abs_neg] using hs.2.1) hT stop hstop (θ*δ)).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
          simpa only [neg_sq,neg_mul] using hs.2.2)))
  have hsub : {z | ∃ K,δ ≤ |censoredNonfoodPrefix c V basal cat T stop z K|} ⊆ E θ ∪ E (-θ) := by
    intro z hz
    obtain ⟨K,hK⟩ := hz
    rcases le_abs.mp hK with hp|hm
    · apply Or.inl
      apply Set.mem_iUnion.mpr
      exact ⟨K,K,le_rfl,mul_le_mul_of_nonneg_left hp hs.1⟩
    · apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨K,K,le_rfl,?_⟩
      have hh := mul_le_mul_of_nonneg_left hm hs.1
      simpa only [mul_neg,neg_mul] using hh
  calc
    _ ≤ μ (E θ ∪ E (-θ)) := measure_mono hsub
    _ ≤ μ (E θ)+μ (E (-θ)) := measure_union_le _ _
    _ ≤ B+B := add_le_add hp hm
    _ = _ := (two_mul B).symm


end
end RandomViability
