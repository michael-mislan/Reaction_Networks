import proofs.OverlappingSiphonInvasion.TrajectoryBounds
import proofs.OverlappingSiphonInvasion.ProductCertificate

noncomputable section
namespace OverlappingSiphonInvasion
open Filter Topology

def productRate (x : State) : ℝ :=
  (field (witness 1) x 1+field (witness 1) x 3)*(x 2+2*x 3) +
  (x 1+x 3)*(field (witness 1) x 2+2*field (witness 1) x 3)

theorem productRate_corrected (x : State) :
    productRate x + (field (witness 1) x 0)*siphonProduct (x 1) (x 2) (x 3)/2 =
      correctedProductDrift (x 0) (x 1) (x 2) (x 3) := by
  simp [productRate, field, witness, siphonProduct, correctedProductDrift]
  ring

def productFloor : ℝ := (1/25)/(2*(14*Real.exp (1*0)))*Real.exp (1*(-5/2))

theorem productFloor_pos : 0 < productFloor := by unfold productFloor; positivity

/-- Uniform extinction-boundary exclusion for the literal invading witness.
No local repulsion or asymptotic floor is supplied as an input. -/
theorem eventually_product_floor (X : ℝ → State) (h : IsTrajectory (witness 1) X) :
    ∀ᶠ t in atTop, productFloor < siphonProduct (X t 1) (X t 2) (X t 3) := by
  obtain ⟨T,hT⟩ := eventually_atTop.1
    ((eventually_total_close X h).and ((eventually_infected_bounds X h).and
      (eventually_ge_atTop (0:ℝ))))
  apply RobustPermanence.bounded_corrector_eventual_floor
    (fun t => siphonProduct (X t 1) (X t 2) (X t 3))
    (fun t => productRate (X t)) (fun t => -X t 0/2)
    (fun t => -field (witness 1) (X t) 0/2)
    T 1 (1/25) 14 (-5/2) 0 (by norm_num) (by norm_num) (by norm_num)
  · intro t ht
    have hp := h.positive t (hT t ht).2.2
    have ha := hp 1
    have hb := hp 2
    have hc := hp 3
    dsimp [siphonProduct]
    positivity
  · intro t ht
    have hs := h.positive t (hT t ht).2.2 0
    have ha := h.positive t (hT t ht).2.2 1
    have hb := h.positive t (hT t ht).2.2 2
    have hc := h.positive t (hT t ht).2.2 3
    have hn := (abs_le.mp (hT t ht).1).2
    dsimp [total] at hn
    constructor <;> linarith
  · intro t ht
    have hd := h.derivative t (hT t ht).2.2
    exact ((hd 1).add (hd 3)).mul ((hd 2).add ((hd 3).const_mul 2))
  · intro t ht
    exact ((h.derivative t (hT t ht).2.2 0).neg).div_const 2
  · intro t ht
    have hp := h.positive t (hT t ht).2.2
    have hg := corrected_logistic (X t 0) (X t 1) (X t 2) (X t 3)
      (hp 1).le (hp 2).le (hp 3).le (hT t ht).2.1.1 (hT t ht).2.1.2 (hT t ht).1
    rw [← productRate_corrected] at hg
    nlinarith only [hg]

def massFloor : ℝ := productFloor/10
theorem massFloor_pos : 0 < massFloor := div_pos productFloor_pos (by norm_num)

theorem eventually_siphon_masses (X : ℝ → State) (h : IsTrajectory (witness 1) X) :
    ∀ᶠ t in atTop, massFloor ≤ X t 1+X t 3 ∧ massFloor ≤ X t 2+2*X t 3 := by
  filter_upwards [eventually_product_floor X h,eventually_infected_bounds X h,
    eventually_ge_atTop (0:ℝ)] with t hP hI ht
  have hp := h.positive t ht
  have ha := (hp 1).le
  have hb := (hp 2).le
  have hc := (hp 3).le
  have hu : 0 ≤ X t 1+X t 3 := by positivity
  have hv : 0 ≤ X t 2+2*X t 3 := by positivity
  have huu : X t 1+X t 3 ≤ 10 := by dsimp [infected] at hI; linarith
  have hvu : X t 2+2*X t 3 ≤ 10 := by dsimp [infected] at hI; linarith
  have hmul1 := mul_le_mul_of_nonneg_left hvu hu
  have hmul2 := mul_le_mul_of_nonneg_right huu hv
  dsimp [siphonProduct] at hP
  dsimp [massFloor]
  constructor <;> nlinarith only [hP,hmul1,hmul2]

end OverlappingSiphonInvasion
