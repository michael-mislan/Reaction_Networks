import proofs.AssayInformation.Identification
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Group.Convolution

noncomputable section
namespace AssayInformation
open MeasureTheory ProbabilityTheory

/-- Blank hitting time at threshold three in the independent exponential
holding-time construction of the literal pure-birth source. -/
def blankEndpointLaw (b g R : ℝ) : Measure ℝ :=
  (expMeasure (sourceRate b g R 0)).conv
    ((expMeasure (sourceRate b g R 1)).conv (expMeasure (sourceRate b g R 2)))

theorem convolution_reverse (μ ν ρ : Measure ℝ)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    μ.conv (ν.conv ρ) = ρ.conv (ν.conv μ) := by
  rw [← Measure.conv_assoc,Measure.conv_comm (μ.conv ν) ρ,Measure.conv_comm μ ν]

/-- Equality of measures, not only equality of finitely sampled CDF values or transforms. -/
theorem endpoint_law_nonidentification :
    blankEndpointLaw 2 1 6 = blankEndpointLaw (8/3) (2/3) 4 := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0:ℝ) < 2)
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0:ℝ) < 5/2)
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0:ℝ) < 8/3)
  norm_num [blankEndpointLaw,sourceRate]
  exact convolution_reverse _ _ _

end AssayInformation
