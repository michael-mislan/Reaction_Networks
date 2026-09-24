import proofs.ACRZeroDivisors.ReleaseIdeal

namespace ACRZeroDivisors
open MvPolynomial

/-- Expanding the corrected field gives the actual released-product fluxes:
old source consumption occurs at F, and each product group at rates[j]*z[j]. -/
theorem releasedOldField_flux_formula {σ A : Type*} [CommRing A] {n : ℕ}
    (other source : σ → A) (F : A) (rates : Fin (n+1) → Aˣ)
    (w : σ → Fin (n+1) → A) (i : σ) :
    releasedOldField (fun i => other i + ((∑ j, w i j)-source i)*F) F rates w i =
      C (other i-source i*F) + ∑ j, C (w i j) * (C (rates j : A)*X j) := by
  classical
  simp only [releasedOldField,cumulativeRelease,map_add,map_mul,map_sub,map_sum,
    mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
  ring

/-- The first intermediate is produced at flux F and consumed linearly. -/
theorem first_release_equation {A : Type*} [CommRing A] {n : ℕ}
    (F : A) (rates : Fin (n+1) → Aˣ) :
    triangularDifferences (cumulativeRelease F rates) 0 =
      C F - C (rates 0 : A)*X 0 := rfl

/-- Each subsequent intermediate receives the preceding linear flux. -/
theorem later_release_equation {A : Type*} [CommRing A] {n : ℕ}
    (F : A) (rates : Fin (n+1) → Aˣ) (j : Fin n) :
    triangularDifferences (cumulativeRelease F rates) j.succ =
      C (rates j.castSucc : A)*X j.castSucc - C (rates j.succ : A)*X j.succ := by
  simp only [triangularDifferences,Fin.cases_succ,cumulativeRelease]
  ring

end ACRZeroDivisors
