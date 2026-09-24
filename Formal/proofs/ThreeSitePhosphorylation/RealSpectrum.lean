import proofs.ThreeSitePhosphorylation.CrossingQuotient

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 300000

def realCandidate (r x : ℝ) : ℝ := (candidatePolynomial r (x:ℂ)).re

theorem realCandidate_continuous (r : ℝ) : Continuous (realCandidate r) := by
  unfold realCandidate candidatePolynomial
  fun_prop

theorem far_root_signs (r : ℝ) (_hl : (1/4:ℝ) ≤ r) (hu : r ≤ (3/10:ℝ)) :
    realCandidate r (-284) < 0 ∧ 0 < realCandidate r (-283) := by
  constructor <;>
    norm_num [realCandidate,candidatePolynomial,pow_succ,Complex.mul_re,Complex.mul_im] <;>
    linarith

theorem near_root_signs (r : ℝ) (hl : (1/4:ℝ) ≤ r) (_hu : r ≤ (3/10:ℝ)) :
    realCandidate r (-31/10000) < 0 ∧ 0 < realCandidate r (-7/2500) := by
  constructor <;>
    norm_num [realCandidate,candidatePolynomial,pow_succ,Complex.mul_re,Complex.mul_im] <;>
    linarith

def realRootLower : Fin 7 → ℝ := ![-284,-74,-35,-13,-3,-23/100,-31/10000]
def realRootUpper : Fin 7 → ℝ := ![-283,-72,-34,-12,-2,-11/50,-7/2500]

theorem real_root_box_signs (r : ℝ) (_hl : (1/4:ℝ) ≤ r) (_hu : r ≤ (3/10:ℝ))
    (i : Fin 7) :
    (-1:ℝ)^(i:ℕ)*realCandidate r (realRootLower i) < 0 ∧
      0 < (-1:ℝ)^(i:ℕ)*realCandidate r (realRootUpper i) := by
  fin_cases i <;> constructor <;>
    norm_num [realRootLower,realRootUpper,realCandidate,candidatePolynomial,
      pow_succ,Complex.mul_re,Complex.mul_im] <;> linarith

theorem real_root_in_box (r : ℝ) (hl : (1/4:ℝ) ≤ r) (hu : r ≤ (3/10:ℝ))
    (i : Fin 7) : ∃ x : ℝ, x ∈ Set.Icc (realRootLower i) (realRootUpper i) ∧
      realCandidate r x=0 := by
  have hb : realRootLower i ≤ realRootUpper i := by
    fin_cases i <;> norm_num [realRootLower,realRootUpper]
  have hc : Continuous (fun x => (-1:ℝ)^(i:ℕ)*realCandidate r x) :=
    continuous_const.mul (realCandidate_continuous r)
  have hs := real_root_box_signs r hl hu i
  obtain ⟨x,hx,hz⟩ := intermediate_value_Icc hb hc.continuousOn ⟨hs.1.le,hs.2.le⟩
  exact ⟨x,hx,(mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (by norm_num))⟩

theorem real_root_box_order (i j : Fin 7) (h : i<j) : realRootUpper i < realRootLower j := by
  fin_cases i <;> fin_cases j <;> norm_num [realRootLower,realRootUpper] at *

theorem seven_negative_roots (r : ℝ) (hl : (1/4:ℝ) ≤ r) (hu : r ≤ (3/10:ℝ)) :
    ∃ x : Fin 7 → ℝ, StrictMono x ∧ ∀ i, x i < 0 ∧ realCandidate r (x i)=0 := by
  choose x hx hz using real_root_in_box r hl hu
  refine ⟨x,?_,?_⟩
  · intro i j hij
    exact (hx i).2.trans_lt ((real_root_box_order i j hij).trans_le (hx j).1)
  · intro i
    refine ⟨(hx i).2.trans_lt ?_,hz i⟩
    fin_cases i <;> norm_num [realRootUpper]

end
end ThreeSitePhosphorylation
