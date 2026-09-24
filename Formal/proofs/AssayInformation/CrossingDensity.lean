import proofs.AssayInformation.JointFixture
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option maxRecDepth 4096
noncomputable section
namespace AssayInformation
open DiagnosticWindows FiniteCopy MeasureTheory
open scoped BigOperators

def jumpRate (i : Fin 5) : ℝ := (5/2)*(1-eigen5 i)
def densityMode (i : Fin 5) (z : Fin 6) : ℝ := jumpRate i * modes5 i z
def exitFlux (z : Fin 6) : ℝ := if z=4 then 401/500 else 0
def suffixDensity (z : Fin 6) (t : ℝ) : ℝ :=
  ∑ i, Real.exp (-jumpRate i*t)*densityMode i z
def loadingCoeff (i : Fin 5) : ℝ :=
  ∑ n : Fin 5, (4:ℝ)^n.val/(n.val.factorial:ℝ)*modes5 i (loadIndex n.val)
def blankDensity (t : ℝ) : ℝ := suffixDensity 0 t
def loadedDensity (t : ℝ) : ℝ :=
  Real.exp (-4)*∑ i, Real.exp (-jumpRate i*t)*jumpRate i*loadingCoeff i

theorem jumpRate_pos (i : Fin 5) : 0 < jumpRate i := by
  fin_cases i <;> norm_num [jumpRate,eigen5]

theorem densityMode_sum (z : Fin 6) : exitFlux z = ∑ i, densityMode i z := by
  fin_cases z <;> norm_num [exitFlux,densityMode,jumpRate,eigen5,modes5,Fin.sum_univ_succ,Fin.ext_iff]

theorem densityMode_eigen (i : Fin 5) (z : Fin 6) :
    kernel5.step (densityMode i) z = eigen5 i*densityMode i z := by
  unfold densityMode
  rw [kernel5.step_scale,capacity5_eigen]
  ring

theorem suffixDensity_source (z : Fin 6) (t : NNReal) :
    suffixDensity z t = kernel5.poissonized ((5/2)*t) exitFlux z := by
  rw [spectral_survival kernel5 exitFlux densityMode eigen5 densityMode_sum densityMode_eigen]
  unfold suffixDensity
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  simp only [NNReal.coe_mul,NNReal.coe_div,NNReal.coe_ofNat,jumpRate]
  ring

theorem suffixDensity_nonneg (z : Fin 6) (t : NNReal) : 0 ≤ suffixDensity z t := by
  rw [suffixDensity_source]
  unfold FiniteKernel.poissonized
  apply tsum_nonneg
  intro n
  exact mul_nonneg (poissonWeight_nonneg _ _) (kernel5.steps_nonneg n
    (by intro z; unfold exitFlux; split_ifs <;> norm_num) z)

theorem loadedDensity_suffix (t : ℝ) : loadedDensity t =
    Real.exp (-4)*∑ n : Fin 5, (4:ℝ)^n.val/(n.val.factorial:ℝ)*
      suffixDensity (loadIndex n.val) t := by
  unfold loadedDensity loadingCoeff suffixDensity densityMode
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem loadedDensity_nonneg (t : NNReal) : 0 ≤ loadedDensity t := by
  rw [loadedDensity_suffix]
  apply mul_nonneg (Real.exp_pos _).le
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (by positivity) (suffixDensity_nonneg _ _)

theorem exponential_density_integrable (q v a : ℝ) (hq : 0 < q) :
    IntegrableOn (fun t => Real.exp (-q*t)*(q*v)) (Set.Ioi a) :=
  (integrableOn_exp_mul_Ioi (by linarith : -q < 0) a).mul_const _

theorem exponential_density_tail (q v a : ℝ) (hq : 0 < q) :
    (∫ t in Set.Ioi a, Real.exp (-q*t)*(q*v)) = Real.exp (-q*a)*v := by
  rw [integral_mul_const,integral_exp_mul_Ioi (by linarith : -q < 0)]
  have hn := ne_of_gt hq
  field_simp

theorem suffixDensity_integrable (z : Fin 6) (a : ℝ) :
    IntegrableOn (suffixDensity z) (Set.Ioi a) := by
  unfold suffixDensity densityMode
  exact integrable_finsetSum _ (fun i _ => exponential_density_integrable _ _ _ (jumpRate_pos i))

theorem suffixDensity_tail (z : Fin 6) (a : ℝ) :
    (∫ t in Set.Ioi a, suffixDensity z t) =
      ∑ i, Real.exp (-jumpRate i*a)*modes5 i z := by
  unfold suffixDensity densityMode
  rw [integral_finsetSum _ (fun i _ => exponential_density_integrable _ _ _ (jumpRate_pos i))]
  apply Finset.sum_congr rfl
  intro i _
  exact exponential_density_tail _ _ _ (jumpRate_pos i)

theorem blankDensity_tail_source (t : NNReal) :
    (∫ s in Set.Ioi (t:ℝ), blankDensity s) = 1-blank5 t := by
  unfold blankDensity
  rw [suffixDensity_tail]
  unfold blank5
  rw [capacity5_survival]
  simp only [sub_sub_cancel]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  simp only [NNReal.coe_mul,NNReal.coe_div,NNReal.coe_ofNat,jumpRate]
  ring

theorem loadedDensity_integrable (a : ℝ) :
    IntegrableOn loadedDensity (Set.Ioi a) := by
  rw [show loadedDensity = (fun t => Real.exp (-4)*∑ n : Fin 5,
    (4:ℝ)^n.val/(n.val.factorial:ℝ)*suffixDensity (loadIndex n.val) t) from
      funext loadedDensity_suffix]
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro n _
  exact (suffixDensity_integrable _ _).const_mul _

theorem loadedDensity_tail_source (t : NNReal) :
    (∫ s in Set.Ioi (t:ℝ), loadedDensity s) = miss5 t := by
  simp only [loadedDensity_suffix]
  rw [integral_const_mul,integral_finsetSum _
    (fun n _ => (suffixDensity_integrable (loadIndex n.val) t).const_mul _)]
  simp_rw [integral_const_mul,suffixDensity_tail]
  unfold miss5
  rw [show kernel5 = birthKernel rates5 rates5_valid from rfl,loading_finite]
  change _ = ∑ n ∈ Finset.range 5, poissonWeight 4 n * kernel5.poissonized
    ((5/2)*t) uncalled (loadIndex n)
  simp_rw [capacity5_survival]
  norm_num [Fin.sum_univ_succ,Finset.sum_range_succ,poissonWeight,loadIndex,
    Nat.factorial,jumpRate,eigen5,modes5]
  ring

theorem blank5_zero : blank5 0 = 0 := by
  unfold blank5
  rw [capacity5_survival]
  norm_num [eigen5,modes5,Fin.sum_univ_succ]

theorem blankDensity_total : (∫ t in Set.Ioi 0, blankDensity t) = 1 := by
  simpa [blank5_zero] using blankDensity_tail_source 0

theorem loaded_atom_nonneg : 0 ≤ 1-miss5 0 := by
  have h : miss5 0 ≤ 1 := by
    unfold miss5 loadedSurvival
    rw [← (poissonWeight_sum 4).tsum_eq]
    apply Summable.tsum_le_tsum
    · intro n
      apply mul_le_of_le_one_right (poissonWeight_nonneg _ _)
      rw [uncalled_indicator]
      exact (kernel5.poissonized_event_bounds _ _ _).2
    · exact loading_summable _ _ _
    · exact (poissonWeight_sum _).summable
  linarith

end AssayInformation
