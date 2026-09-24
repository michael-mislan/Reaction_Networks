import proofs.ResourceLimitedCompetition.ChemicalProbability
import proofs.ResourceLimitedCompetition.ErrorDecay
namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy Filter
open scoped Topology

theorem chemical_raw_sharp (N : ℕ) (M t : ℝ) (hM : 0 ≤ M) (ht : 0 ≤ t) :
    chemicalRawError N M t ≤ M*(32+t*chemicalScale N/42)*Real.exp (-(3/2)*chemicalScale N) := by
  have hu := chemicalScale_nonneg N
  have h1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (by linarith only [hu] : -12*chemicalScale N ≤ -(3/2)*chemicalScale N))
    (by positivity : 0 ≤ 7*M)
  have h2 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (by linarith only [hu] : -(31/2)*chemicalScale N ≤ -(3/2)*chemicalScale N))
    (by positivity : 0 ≤ (M*t/84)*chemicalScale N)
  have hs : 2*chemicalScale N-(N : ℝ)/1000000000000000 ≤ -(3/2)*chemicalScale N := by
    unfold chemicalScale localAlpha innerEnergy outerEnergy
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith only [hn]
  have h3 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) hM
  have hp : -(N : ℝ)*(1/1000000)^2/35 ≤ -(3/2)*chemicalScale N := by
    unfold chemicalScale localAlpha innerEnergy outerEnergy
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith only [hn]
  have h5 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hp) (by positivity : 0 ≤ 24*M)
  unfold chemicalRawError
  nlinarith only [h1,h2,h3,h5]

theorem chemical_raw_double_exponent (N : ℕ) (M t : ℝ) (hM : 0 ≤ M) (ht : 0 ≤ t) :
    chemicalRawError N M t ≤ M*(32+t/21)*Real.exp (-chemicalScale N) := by
  have hu := chemicalScale_nonneg N
  have he : chemicalScale N ≤ 2*Real.exp (chemicalScale N/2) := by
    linarith only [Real.add_one_le_exp (chemicalScale N/2)]
  have h := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(3/2)*chemicalScale N)).le
  have hi : 2*Real.exp (chemicalScale N/2)*Real.exp (-(3/2)*chemicalScale N)=
      2*Real.exp (-chemicalScale N) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [hi] at h
  have hscaled := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ M*t/42)
  have hbase := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (by linarith only [hu] : -(3/2)*chemicalScale N ≤ -chemicalScale N)) (by positivity : 0 ≤ 32*M)
  have hb := chemical_raw_sharp N M t hM ht
  nlinarith only [hb,hscaled,hbase]

theorem exponential_log_budget (K a : ℕ → ℝ) (hK : ∀ N, 0 < K N)
    (h : Tendsto (fun N => Real.log (K N)-a N) atTop atBot) :
    Tendsto (fun N => K N*Real.exp (-a N)) atTop (𝓝 0) := by
  have he := Real.tendsto_exp_atBot.comp h
  have hi : (fun N => Real.exp (Real.log (K N)-a N))=(fun N => K N*Real.exp (-a N)) := by
    funext N
    rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (hK N)]
  simpa only [Function.comp_def,hi] using he

end ResourceLimitedCompetition
