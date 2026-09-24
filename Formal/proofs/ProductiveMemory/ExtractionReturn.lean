import proofs.ProductiveMemory.ExtractionInterval
import proofs.ProductiveMemory.ExtractionLocal

namespace ProductiveMemory
open FiniteCopy Set
noncomputable section
set_option Elab.async false

theorem low_extraction_box (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000)) :
    reducedA rho z ∈ Icc 12 14 ∧ reducedB z ∈ Icc (201224/10000) (201227/10000) := by
  have hd : 0 < z+2 := by linarith [hz.1]
  have hb : reducedB z ∈ Icc (201224/10000) (201227/10000) := by
    unfold reducedB
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith [hz.2]
    · apply (div_le_iff₀ hd).mpr
      linarith [hz.1]
  have hs : z^2 ∈ Icc ((98/100:ℝ)^2) ((99/100:ℝ)^2) := by
    constructor <;> nlinarith [hz.1,hz.2]
  have hzb : z*reducedB z ∈ Icc (197/10:ℝ) (198/10) := by
    constructor <;> nlinarith [hz.1,hz.2,hb.1,hb.2]
  have hrz : rho*z ∈ Icc (0:ℝ) (1/10) := by
    constructor <;> nlinarith [hr.1,hr.2,hz.1,hz.2]
  refine ⟨?_,hb⟩
  unfold reducedA reducedK
  norm_num only
  constructor <;> nlinarith [hs.1,hs.2,hzb.1,hzb.2,hrz.1,hrz.2,hz.1,hz.2]

theorem high_extraction_box (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000)) :
    reducedA rho z ∈ Icc 20 22 ∧ reducedB z ∈ Icc (122694/10000) (122697/10000) := by
  have hd : 0 < z+2 := by linarith [hz.1]
  have hb : reducedB z ∈ Icc (122694/10000) (122697/10000) := by
    unfold reducedB
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith [hz.2]
    · apply (div_le_iff₀ hd).mpr
      linarith [hz.1]
  have hs : z^2 ∈ Icc ((289/100:ℝ)^2) ((290/100:ℝ)^2) := by
    constructor <;> nlinarith [hz.1,hz.2]
  have hzb : z*reducedB z ∈ Icc (354/10:ℝ) (356/10) := by
    constructor <;> nlinarith [hz.1,hz.2,hb.1,hb.2]
  have hrz : rho*z ∈ Icc (0:ℝ) (1/10) := by
    constructor <;> nlinarith [hr.1,hr.2,hz.1,hz.2]
  refine ⟨?_,hb⟩
  unfold reducedA reducedK
  norm_num only
  constructor <;> nlinarith [hs.1,hs.2,hzb.1,hzb.2,hrz.1,hrz.2,hz.1,hz.2]

theorem extraction_remainder_identity (rho : ℝ) (s y : Point) :
    extractDrift rho 0 (fun i => s i+y i) = fun i =>
      extractDrift rho 0 s i+extractionLinear (s 0) (s 1) (s 2) rho y i+sourceRemainder y i := by
  unfold extractDrift extractionLinear
  rw [source_remainder_identity]
  ext i
  fin_cases i <;> norm_num
  ring

theorem low_extraction_dissipation (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (y : Point)
    (hy : ∀ i, |y i| ≤ 1/400) :
    2*lowExtractionPair y (extractDrift rho 0 (fun i => lift rho z i+y i)) ≤
      -(59/100)*normSq y := by
  have hb := low_extraction_box rho z hr hz
  have hl := low_extraction_linear (reducedA rho z) (reducedB z) z rho y
    (by norm_num at hb ⊢; exact hb.1) (by norm_num at hb ⊢; exact hb.2)
    (by norm_num at hz ⊢; exact hz) (by norm_num at hr ⊢; exact hr)
  have hc := low_extraction_cubic y hy
  rw [extraction_remainder_identity,he]
  simp only [Pi.zero_apply,zero_add]
  have hid : lowExtractionPair y (fun i => extractionLinear
      (lift rho z 0) (lift rho z 1) (lift rho z 2) rho y i+sourceRemainder y i) =
      lowExtractionPair y (extractionLinear (reducedA rho z) (reducedB z) z rho y)+
      lowExtractionPair y (sourceRemainder y) := by
    norm_num [lift,lowExtractionPair,Matrix.cons_val_two,Matrix.cons_val_three]
    ring
  rw [hid]
  linarith only [hl,hc]

theorem high_extraction_dissipation (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (y : Point)
    (hy : ∀ i, |y i| ≤ 1/400) :
    2*highExtractionPair y (extractDrift rho 0 (fun i => lift rho z i+y i)) ≤
      -(59/100)*normSq y := by
  have hb := high_extraction_box rho z hr hz
  have hl := high_extraction_linear (reducedA rho z) (reducedB z) z rho y
    (by norm_num at hb ⊢; exact hb.1) (by norm_num at hb ⊢; exact hb.2)
    (by norm_num at hz ⊢; exact hz) (by norm_num at hr ⊢; exact hr)
  have hc := high_extraction_cubic y hy
  rw [extraction_remainder_identity,he]
  simp only [Pi.zero_apply,zero_add]
  have hid : highExtractionPair y (fun i => extractionLinear
      (lift rho z 0) (lift rho z 1) (lift rho z 2) rho y i+sourceRemainder y i) =
      highExtractionPair y (extractionLinear (reducedA rho z) (reducedB z) z rho y)+
      highExtractionPair y (sourceRemainder y) := by
    norm_num [lift,highExtractionPair,Matrix.cons_val_two,Matrix.cons_val_three]
    ring
  rw [hid]
  linarith only [hl,hc]

end
end ProductiveMemory
