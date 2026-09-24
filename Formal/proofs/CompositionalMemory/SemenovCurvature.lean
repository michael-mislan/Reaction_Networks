import proofs.CompositionalMemory.SemenovFieldTaylor
import proofs.CompositionalMemory.SemenovMetricConsequences
import proofs.CompositionalMemory.QuadraticCurvatureBounds

namespace CompositionalMemory.Semenov
open Matrix

/-- The actual eleven-channel Taylor remainder consumes at most48 percent
of the Euclidean restoring term throughout the checked metric tube. -/
theorem field_remainder_work_bound
    (zc : Fin 8 → Fin 17 → ℚ) (pc wc : Fin 8 → Fin 8 → Fin 17 → ℚ)
    (A : Fin 8 → Fin 8 → ℚ) (nr : Fin 11 → ℚ) (eta radius margin L Q H : ℚ)
    (hg : MetricGeometryChecks zc pc wc A nr eta radius margin L Q H)
    (t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1) (x : Fin 8 → ℝ)
    (hx : vectorSquares x ≤ (radius : ℝ)^2) :
    (∑ r,2*(∑ i,x i*((coefficientMatrix pc t).mulVec (fun j => (stoich r j : ℝ))) i)*chemicalQuadratic x r) ≤
      (12/25 : ℝ)*vectorSquares x := by
  rcases hg with ⟨hpos,htri,hdiag,hmargin,hnr,hcurv,heta,hL,hH,hJ,hQ⟩
  have hr : (0 : ℝ) ≤ radius := by exact_mod_cast hpos.2.1.le
  have hs (r : Fin 11) :
      2*(∑ i,x i*((coefficientMatrix pc t).mulVec (fun j => (stoich r j : ℝ))) i)*chemicalQuadratic x r ≤
        (if r.val=7 then 0 else nominalRate r*(nr r : ℝ))*(radius : ℝ)*vectorSquares x := by
    by_cases h7 : r.val=7
    · simp [chemicalQuadratic,h7]
    · have hn : (0 : ℝ) ≤ nr r := by exact_mod_cast (hnr r).1
      have hp := metric_jump_norm_bound pc nr (fun r => (hnr r).2) t hl hu r
      have hh := (le_abs_self _).trans (single_reaction_curvature_bound x
        ((coefficientMatrix pc t).mulVec (fun j => (stoich r j : ℝ)))
        (reactantA r) (reactantB r) (radius : ℝ) (nr r : ℝ) (nominalRate r)
        (bimolecular_reactants_distinct r h7) hr hn (nominalRate_nonneg r) hx hp)
      simp only [chemicalQuadratic,if_neg h7]
      convert hh using 1
      ring
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hs r)
  have hc : (∑ r,if r.val=7 then (0 : ℝ) else nominalRate r*(nr r : ℝ))*(radius : ℝ) ≤ (12/25 : ℝ) := by
    have he : (curvatureUpper nr : ℝ)=∑ r,if r.val=7 then (0 : ℝ) else nominalRate r*(nr r : ℝ) := by
      simp only [curvatureUpper,Rat.cast_sum,apply_ite,Rat.cast_zero,Rat.cast_mul,kineticRational_cast]
    rw [← he]
    have hh := Rat.cast_mono (K := ℝ) hcurv
    norm_num only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh
    exact hh
  simp only [← Finset.sum_mul] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_right hc (vectorSquares_nonneg x))

end CompositionalMemory.Semenov
