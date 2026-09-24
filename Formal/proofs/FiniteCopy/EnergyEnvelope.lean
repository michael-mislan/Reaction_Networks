import proofs.FiniteCopy.LocalGenerator

namespace FiniteCopy

noncomputable def localCeiling : ℝ :=
  localAlpha*100000000*Real.exp (84*localAlpha*100000000)

theorem localCeiling_nonneg : 0 ≤ localCeiling := by
  unfold localCeiling localAlpha
  positivity

theorem energy_drift_envelope (n v V : ℝ) (hn : 0 ≤ n) (hv : 0 ≤ v)
    (hV : V ≤ 42*v) :
    localAlpha*Real.exp (n*localAlpha*V)*(-n/2*v+100000000) ≤ localCeiling := by
  have hnv := mul_nonneg hn hv
  have hm := mul_le_mul_of_nonneg_left hV hn
  have halpha : 0 ≤ localAlpha := by norm_num [localAlpha]
  by_cases h : 100000000 ≤ n*v/2
  · have hf : -n/2*v+100000000 ≤ 0 := by linarith
    have hp : 0 ≤ localAlpha*Real.exp (n*localAlpha*V) := by positivity
    exact (mul_nonpos_of_nonneg_of_nonpos hp hf).trans localCeiling_nonneg
  · have hx : n*localAlpha*V ≤ 84*localAlpha*100000000 := by
      unfold localAlpha
      linarith only [hm,not_le.mp h]
    have he := Real.exp_le_exp.mpr hx
    have hf : -n/2*v+100000000 ≤ 100000000 := by nlinarith only [hnv]
    calc
      localAlpha*Real.exp (n*localAlpha*V)*(-n/2*v+100000000) ≤
          localAlpha*Real.exp (n*localAlpha*V)*100000000 :=
        mul_le_mul_of_nonneg_left hf (mul_nonneg halpha (Real.exp_pos _).le)
      _ ≤ localCeiling := by
        unfold localCeiling
        have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ localAlpha*100000000)
        nlinarith only [hh]

theorem energy_decay_envelope (n v V a : ℝ) (hn : 0 ≤ n)
    (hV : V ≤ 42*v) (ha : a ≤ V) (hNa : 168*100000000 ≤ n*a) :
    localAlpha*Real.exp (n*localAlpha*V)*(-n/2*v+100000000) ≤
      -(n*localAlpha*a/168)*Real.exp (n*localAlpha*V) := by
  have hna := mul_le_mul_of_nonneg_left ha hn
  have hnv := mul_le_mul_of_nonneg_left hV hn
  have hs : -n/2*v+100000000 ≤ -(n*a/168) := by nlinarith only [hna,hnv,hNa]
  have hh := mul_le_mul_of_nonneg_left hs (by unfold localAlpha; positivity :
    0 ≤ localAlpha*Real.exp (n*localAlpha*V))
  nlinarith only [hh]

end FiniteCopy
