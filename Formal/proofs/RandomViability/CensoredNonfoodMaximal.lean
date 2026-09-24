import proofs.RandomViability.CensoredNonfoodTime
import proofs.RandomViability.JumpWaitingSupport

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def censoredNonfoodFluctuationBy {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (δ : ℝ) (K : ℕ) (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  ∃ j,j ≤ K ∧ δ ≤ ∑ i : Fin j,censoredNonfoodCompensation c V basal cat T stop
    i (Preorder.frestrictLe (i : ℕ) z) (z ((i : ℕ)+1))

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_censored_nonfood_crossing_tail (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (θ T : ℝ) (hθ0 : 0 ≤ θ) (hθ : |θ| *((n : ℝ)/V) ≤ 1) (hT : 0 ≤ T)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (δ : ℝ) (K : ℕ) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | censoredNonfoodFluctuationBy c V basal cat T stop δ K z} ≤
      ENNReal.ofReal (Real.exp (-θ*δ+θ^2*((384000+11*(n : ℝ))/V)*T)) := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
  let κ := jumpHistoryKernel unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
    (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  let m := censoredNonfoodMultiplier c V basal cat θ T stop
  let L := θ*δ-θ^2*((384000+11*(n : ℝ))/V)*T
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
  have hsub : W ∩ {z | censoredNonfoodFluctuationBy c V basal cat T stop δ K z} ⊆
      {z | ∃ j,j ≤ K ∧ a ≤ trajectoryProduct m j z} := by
    intro z hz
    obtain ⟨j,hj,hA⟩ := hz.2
    refine ⟨j,hj,?_⟩
    dsimp only [m,a]
    rw [censored_nonfood_product_exp]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have ht := censored_nonfood_time_bound V T hT stop z hz.1 j
    exact sub_le_sub (mul_le_mul_of_nonneg_left hA hθ0)
      (mul_le_mul_of_nonneg_left ht (by positivity))
  have heq : μ (W ∩ {z | censoredNonfoodFluctuationBy c V basal cat T stop δ K z}) =
      μ {z | censoredNonfoodFluctuationBy c V basal cat T stop δ K z} :=
    Measure.measure_inter_eq_of_ae hw
  have ht : a*μ {z | censoredNonfoodFluctuationBy c V basal cat T stop δ K z} ≤ 1 := by
    rw [← heq]
    exact (mul_le_mul_right (measure_mono hsub) a).trans hc
  have hinv : B*a = 1 := by
    dsimp [B,a]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,neg_add_cancel,
      Real.exp_zero,ENNReal.ofReal_one]
  have hb : μ {z | censoredNonfoodFluctuationBy c V basal cat T stop δ K z} ≤ B := by
    calc
      _ = B*(a*μ {z | censoredNonfoodFluctuationBy c V basal cat T stop δ K z}) := by
        rw [← mul_assoc,hinv,one_mul]
      _ ≤ B*1 := mul_le_mul_right ht B
      _ = _ := mul_one _
  have he : -L = -θ*δ+θ^2*((384000+11*(n : ℝ))/V)*T := by dsimp [L]; ring
  simpa only [B,he] using hb

theorem physical_censored_nonfood_any_index_tail (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (θ T : ℝ) (hθ0 : 0 ≤ θ) (hθ : |θ| *((n : ℝ)/V) ≤ 1) (hT : 0 ≤ T)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (δ : ℝ) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      (⋃ K,{z | censoredNonfoodFluctuationBy c V basal cat T stop δ K z}) ≤
      ENNReal.ofReal (Real.exp (-θ*δ+θ^2*((384000+11*(n : ℝ))/V)*T)) := by
  have hm : Monotone (fun K => {z | censoredNonfoodFluctuationBy c V basal cat T stop δ K z}) := by
    intro K J hK z hz
    obtain ⟨j,hj,hA⟩ := hz
    exact ⟨j,hj.trans hK,hA⟩
  rw [hm.measure_iUnion]
  exact iSup_le (fun K => physical_censored_nonfood_crossing_tail hn c V hV basal cat N
    hbasal hcat θ T hθ0 hθ hT stop hstop δ K)

end
end RandomViability
