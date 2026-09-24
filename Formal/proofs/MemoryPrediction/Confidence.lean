import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

namespace MemoryPrediction
noncomputable section
open MeasureTheory ProbabilityTheory

def sampleMean {Ω : Type*} (X : Fin 4000 → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ i, X i ω)/4000

theorem training_exp_bound : Real.exp (-(125/16 : ℝ)) ≤ 1/2000 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 125/16) 21
  have hl : (2000 : ℝ) ≤ Real.exp (125/16) := by
    apply le_trans _ hs
    norm_num [Finset.sum_range_succ,Nat.factorial]
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2000) hl

/-- One-sided finite-data guarantee, proved from independence and boundedness.
The mean is later computed from the actual observation source. -/
theorem bounded_centered_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (X : Fin n → Ω → ℝ) (p ε : ℝ)
    (hm : ∀ i, AEMeasurable (X i) μ) (hi : iIndepFun X μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hp : ∀ i, ∫ ω, X i ω ∂μ = p) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i, (X i ω-p)} ≤ Real.exp (-ε^2/(2*((n : ℝ)*(1/4)))) := by
  let Y := fun i ω => X i ω-p
  have hY : iIndepFun Y μ := by
    exact hi.comp (fun _ x => x-p) (fun _ => measurable_id.sub_const p)
  have hG (i : Fin n) : HasSubgaussianMGF (Y i) (1/4) μ := by
    have h := hasSubgaussianMGF_of_mem_Icc (hm i) (hb i)
    norm_num [hp i,Y] at h
    exact h
  have ht := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY
    (c := fun _ => (1/4 : NNReal)) (s := Finset.univ)
    (fun i _ => hG i) (ε := ε) hε
  simpa [Y] using ht

theorem centered_sum_identity {Ω : Type*} (n : ℕ) (X : Fin n → Ω → ℝ) (p : ℝ) (ω : Ω) :
    (∑ i, (X i ω-p)) = (∑ i, X i ω)-(n : ℝ)*p := by
  simp [Finset.sum_sub_distrib]

theorem bounded_sample_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin 4000 → Ω → ℝ) (p : ℝ)
    (hm : ∀ i, AEMeasurable (X i) μ) (hi : iIndepFun X μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | p+1/32 ≤ sampleMean X ω} ≤ 1/2000 := by
  have ht := bounded_centered_upper μ 4000 X p 125 hm hi hb hp (by norm_num)
  norm_num only [Nat.cast_ofNat] at ht
  have hs : {ω | p+1/32 ≤ sampleMean X ω} ⊆ {ω | 125 ≤ ∑ i, (X i ω-p)} := by
    intro ω hω
    change 125 ≤ ∑ i,(X i ω-p)
    rw [centered_sum_identity]
    norm_num only [Nat.cast_ofNat]
    change p+1/32 ≤ (∑ i,X i ω)/4000 at hω
    linarith
  exact ((measureReal_mono hs (by finiteness)).trans ht).trans training_exp_bound

theorem bounded_sample_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin 4000 → Ω → ℝ) (p : ℝ)
    (hm : ∀ i, AEMeasurable (X i) μ) (hi : iIndepFun X μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | sampleMean X ω ≤ p-1/32} ≤ 1/2000 := by
  let Z := fun i ω => 1-X i ω
  have hZ : iIndepFun Z μ := hi.comp (fun _ x => 1-x) (fun _ => measurable_const.sub measurable_id)
  have hZm (i) : AEMeasurable (Z i) μ := (hm i).const_sub 1
  have hZb (i) : ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hb i] with ω hω
    dsimp [Z]
    constructor <;> linarith [hω.1,hω.2]
  have hZp (i) : ∫ ω,Z i ω ∂μ = 1-p := by
    rw [show Z i = (fun ω => 1-X i ω) from rfl,
      integral_sub (integrable_const _) (Integrable.of_mem_Icc 0 1 (hm i) (hb i)),
      integral_const,hp i]
    simp
  have h := bounded_sample_upper μ Z (1-p) hZm hZ hZb hZp
  have he (ω) : sampleMean Z ω = 1-sampleMean X ω := by
    simp [sampleMean,Z,Finset.sum_sub_distrib]
    ring
  have hs : {ω | sampleMean X ω ≤ p-1/32} = {ω | (1-p)+1/32 ≤ sampleMean Z ω} := by
    ext ω
    rw [Set.mem_setOf_eq,Set.mem_setOf_eq,he]
    constructor <;> intro hh <;> linarith
  rw [hs]
  exact h

end
end MemoryPrediction
