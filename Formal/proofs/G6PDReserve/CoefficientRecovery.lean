import proofs.G6PDReserve.ObservationRecovery
import proofs.G6PDReserve.FunctionalIdentification

namespace G6PDReserve
noncomputable section
open Set
open scoped BigOperators

def rateFromCoefficients (β : Six) (P S A B g : ℝ) : ℝ :=
  scalarRate (β 0+β 1/S) (β 3/S) ((β 2+β 4*A+β 5*B)/S) P g

theorem coefficient_denominator (β : Six) (P S A B R : ℝ)
    (hS : S ≠ 0) (hR : P-R ≠ 0) :
    ((β 0+β 1/S)*(P-R)+(β 3/S)*R+(β 2+β 4*A+β 5*B)/S)/(P-R) =
      dot (feature (P-R) S R A B) β := by
  simp [dot,feature,Fin.sum_univ_succ]
  field_simp
  ring

/-- All coefficient-vector calculations describe the original literal kinetic
class, not a new phenomenological field. -/
theorem coefficient_rate_is_literal (β : Six) (hβ : PositiveSix β)
    (P S A B g : ℝ) (hS : 0 < S) (hg : g < P) :
    shimoRate (parameters β 0) (parameters β 2) (parameters β 1)
      (parameters β 3) (parameters β 4) (parameters β 5) (P-g) S g A B =
      rateFromCoefficients β P S A B g := by
  have hp := parameters_positive β hβ
  have hn : ∀ i, β i ≠ 0 := fun i => ne_of_gt (hβ i)
  apply inv_injective
  rw [reciprocal_source_rate _ _ _ _ _ _ _ _ _ _ _
    (ne_of_gt (hp 0)) (ne_of_gt (sub_pos.mpr hg)) (ne_of_gt hS)
    (ne_of_gt (hp 2)) (ne_of_gt (hp 1))]
  unfold rateFromCoefficients scalarRate
  rw [inv_div]
  simp [parameters]
  field_simp [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5,ne_of_gt hS,ne_of_gt (sub_pos.mpr hg)]
  ring

theorem coefficient_rate_is_literal_on_pool (β : Six) (hβ : PositiveSix β)
    (P S A B g : ℝ) (hS : 0 < S) (hg : g ≤ P) :
    shimoRate (parameters β 0) (parameters β 2) (parameters β 1)
      (parameters β 3) (parameters β 4) (parameters β 5) (P-g) S g A B =
      rateFromCoefficients β P S A B g := by
  rcases lt_or_eq_of_le hg with h | rfl
  · exact coefficient_rate_is_literal β hβ P S A B g hS h
  · simp [shimoRate, rateFromCoefficients, scalarRate]

/-- A verified finite dual observation certificate implies existence and a
uniform deadline in the full positive six-coefficient class. -/
theorem certified_observations_recover {ι : Type*} [Fintype ι]
    (F : ι → Six) (rhs y : ι → ℝ) (β : Six) (hβ : PositiveSix β)
    (P S A B q x R U : ℝ) (hP : 0 < P) (hS : 0 < S)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 0 < q)
    (hx : 0 ≤ x) (hxR : x < R) (hRP : R < P)
    (hy : ∀ i, 0 ≤ y i) (hobs : ∀ i, dot (F i) β ≤ rhs i)
    (hcert : ∀ j, feature (P-R) S R A B j = ∑ i, y i*F i j)
    (hbudget : ∑ i, y i*rhs i ≤ U) (hmargin : q < 1/U) :
    ∃ g : ℝ → ℝ, g 0 = x ∧
      (∀ t ∈ Icc 0 ((R-x)/(1/U-q)), g t ∈ Icc 0 P) ∧
      (∀ t ∈ Icc 0 ((R-x)/(1/U-q)), HasDerivAt g
        (shimoRate (parameters β 0) (parameters β 2) (parameters β 1)
          (parameters β 3) (parameters β 4) (parameters β 5) (P-g t) S (g t) A B-q) t) ∧
      ∃ t ∈ Icc (0:ℝ) ((R-x)/(1/U-q)), R ≤ g t := by
  let a := β 0+β 1/S
  let b := β 3/S
  let c := (β 2+β 4*A+β 5*B)/S
  have ha : 0 < a := add_pos (hβ 0) (div_pos (hβ 1) hS)
  have hb : 0 < b := div_pos (hβ 3) hS
  have hc : 0 < c := by
    have h2 := hβ 2; have h4 := hβ 4; have h5 := hβ 5
    dsimp [c]; positivity
  have hRR : R ∈ Icc 0 P := ⟨by linarith,hRP.le⟩
  have hxx : x ∈ Icc 0 P := ⟨hx,by linarith⟩
  have hD : (a*(P-R)+b*R+c)/(P-R) ≤ U := by
    rw [show (a*(P-R)+b*R+c)/(P-R) = dot (feature (P-R) S R A B) β from
      coefficient_denominator β P S A B R (ne_of_gt hS) (ne_of_gt (sub_pos.mpr hRP))]
    exact le_trans (finite_upper_certificate F rhs y (feature (P-R) S R A B) β hy hobs hcert) hbudget
  have hlow (z : ℝ) (hz : z ∈ Icc 0 P) (hzR : z ≤ R) :
      1/U-q ≤ scalarRate a b c P z-q :=
    scalar_drift_certificate a b c P R z U q ha hb hc hP hz hRR hzR hRP hD
  have hbd : q ≤ scalarRate a b c P 0 := by
    have := hlow 0 ⟨le_rfl,hP.le⟩ hRR.1
    linarith
  have hm : 0 < 1/U-q := sub_pos.mpr hmargin
  have hT : 0 ≤ (R-x)/(1/U-q) := (div_pos (sub_pos.mpr hxR) hm).le
  obtain ⟨g,h0,hpool,hd⟩ := scalar_solution_exists a b c P q x _ ha hb hc hP hq hxx hT hbd
  have htime : (R-g 0)/(1/U-q) = (R-x)/(1/U-q) := by rw [h0]
  have hhit := positive_drift_reaches g R (1/U-q) hm (by rw [h0]; exact hxR)
    (by rw [htime]; intro t ht; simpa only [(hd t ht).deriv] using hd t ht)
    (by rw [htime]; intro t ht hh; rw [(hd t ht).deriv]; exact hlow (g t) (hpool t ht) hh.le)
  rw [htime] at hhit
  refine ⟨g,h0,hpool,?_,hhit⟩
  intro t ht
  rw [coefficient_rate_is_literal_on_pool β hβ P S A B (g t) hS (hpool t ht).2]
  exact hd t ht

end
end G6PDReserve
