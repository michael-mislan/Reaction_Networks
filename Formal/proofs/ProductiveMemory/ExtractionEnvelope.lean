import proofs.ProductiveMemory.ExtractionGenerator

namespace ProductiveMemory
open FiniteCopy
noncomputable section
set_option Elab.async false

def extractionCeiling : ℝ := localAlpha*100000000*Real.exp (120*localAlpha*100000000)

theorem extractionCeiling_nonneg : 0 ≤ extractionCeiling := by
  unfold extractionCeiling localAlpha
  positivity

theorem extraction_drift_envelope (n v E : ℝ) (hn : 0 ≤ n) (hv : 0 ≤ v)
    (hE : E ≤ 60*v) :
    localAlpha*Real.exp (n*localAlpha*E)*(-n/2*v+100000000) ≤ extractionCeiling := by
  have hnv := mul_nonneg hn hv
  have hm := mul_le_mul_of_nonneg_left hE hn
  have halpha : 0 ≤ localAlpha := by norm_num [localAlpha]
  by_cases h : 100000000 ≤ n*v/2
  · have hf : -n/2*v+100000000 ≤ 0 := by linarith
    have hp : 0 ≤ localAlpha*Real.exp (n*localAlpha*E) := by positivity
    exact (mul_nonpos_of_nonneg_of_nonpos hp hf).trans extractionCeiling_nonneg
  · have hx : n*localAlpha*E ≤ 120*localAlpha*100000000 := by
      unfold localAlpha
      linarith only [hm,not_le.mp h]
    have he := Real.exp_le_exp.mpr hx
    have hf : -n/2*v+100000000 ≤ 100000000 := by nlinarith only [hnv]
    calc
      localAlpha*Real.exp (n*localAlpha*E)*(-n/2*v+100000000) ≤
          localAlpha*Real.exp (n*localAlpha*E)*100000000 :=
        mul_le_mul_of_nonneg_left hf (mul_nonneg halpha (Real.exp_pos _).le)
      _ ≤ extractionCeiling := by
        unfold extractionCeiling
        have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ localAlpha*100000000)
        nlinarith only [hh]

theorem extraction_decay_envelope (n v E a : ℝ) (hn : 0 ≤ n)
    (hE : E ≤ 60*v) (ha : a ≤ E) (hNa : 240*100000000 ≤ n*a) :
    localAlpha*Real.exp (n*localAlpha*E)*(-n/2*v+100000000) ≤
      -(n*localAlpha*a/240)*Real.exp (n*localAlpha*E) := by
  have hna := mul_le_mul_of_nonneg_left ha hn
  have hnv := mul_le_mul_of_nonneg_left hE hn
  have hs : -n/2*v+100000000 ≤ -(n*a/240) := by nlinarith only [hna,hnv,hNa]
  have hh := mul_le_mul_of_nonneg_left hs (by unfold localAlpha; positivity :
    0 ≤ localAlpha*Real.exp (n*localAlpha*E))
  nlinarith only [hh]

theorem extraction_affine_envelope (n v E a : ℝ) (hn : 0 ≤ n) (hv : 0 ≤ v)
    (ha : 0 ≤ a) (hE : E ≤ 60*v) (hNa : 480*100000000 ≤ n*a) :
    localAlpha*Real.exp (n*localAlpha*E)*(-n/2*v+100000000) ≤
      -(n*localAlpha*a/480)*Real.exp (n*localAlpha*E)+
      (n*localAlpha*a/480)*(2*Real.exp (n*localAlpha*a/2)) := by
  have halpha : 0 ≤ localAlpha := by norm_num [localAlpha]
  have hk : 0 ≤ n*localAlpha*a/480 := by positivity
  by_cases hh : a/2 ≤ E
  · have hd := extraction_decay_envelope n v E (a/2) hn hE hh (by nlinarith only [hNa])
    have hp : 0 ≤ (n*localAlpha*a/480)*(2*Real.exp (n*localAlpha*a/2)) := by positivity
    nlinarith only [hd,hp]
  · have hex : Real.exp (n*localAlpha*E) ≤ Real.exp (n*localAlpha*a/2) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left (le_of_not_ge hh) (mul_nonneg hn halpha)
      nlinarith only [hm]
    have hnv := mul_nonneg hn hv
    have hs : -n/2*v+100000000 ≤ 100000000 := by nlinarith only [hnv]
    have hfirst := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ localAlpha*Real.exp (n*localAlpha*E))
    have hsecond := mul_le_mul_of_nonneg_left hex (by positivity : 0 ≤ localAlpha*100000000)
    have hthird := mul_le_mul_of_nonneg_left hNa (by positivity : 0 ≤ localAlpha*Real.exp (n*localAlpha*a/2))
    have hfourth := mul_le_mul_of_nonneg_left hex hk
    nlinarith only [hfirst,hsecond,hthird,hfourth]

end
end ProductiveMemory
