import Mathlib

namespace OptimalAffinityCorrected

noncomputable section

def reconstructedReverseFlux (J g q : ℝ) : ℝ := J * g / (q - 1)
def reconstructedForwardFlux (J g q : ℝ) : ℝ := J * g * q / (q - 1)

theorem reconstructedFluxes_firstOrder
    (J g q : ℝ) (hJ : 0 < J) (hg : 0 < g) (hq : 1 < q) :
    0 < reconstructedReverseFlux J g q ∧
    0 < reconstructedForwardFlux J g q ∧
    reconstructedForwardFlux J g q - reconstructedReverseFlux J g q = J * g ∧
    reconstructedForwardFlux J g q / reconstructedReverseFlux J g q = q := by
  have hden : 0 < q - 1 := by linarith
  have hJg : 0 < J * g := mul_pos hJ hg
  have hrev : 0 < reconstructedReverseFlux J g q := by
    exact div_pos hJg hden
  have hfwd : 0 < reconstructedForwardFlux J g q := by
    unfold reconstructedForwardFlux
    positivity
  refine ⟨hrev, hfwd, ?_, ?_⟩
  · unfold reconstructedForwardFlux reconstructedReverseFlux
    field_simp [ne_of_gt hden]
  · unfold reconstructedForwardFlux reconstructedReverseFlux
    field_simp [ne_of_gt hden, ne_of_gt hJ, ne_of_gt hg]

def reconstructedRate (oneWayFlux monomialAtPoint : ℝ) : ℝ :=
  oneWayFlux / monomialAtPoint

theorem reconstructedRate_positive_and_reproduces
    (oneWayFlux monomialAtPoint : ℝ)
    (hflux : 0 < oneWayFlux) (hmonomial : 0 < monomialAtPoint) :
    0 < reconstructedRate oneWayFlux monomialAtPoint ∧
      reconstructedRate oneWayFlux monomialAtPoint * monomialAtPoint = oneWayFlux := by
  constructor
  · exact div_pos hflux hmonomial
  · unfold reconstructedRate
    field_simp [ne_of_gt hmonomial]

end
end OptimalAffinityCorrected
