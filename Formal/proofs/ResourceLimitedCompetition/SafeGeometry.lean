import proofs.ResourceLimitedCompetition.AffineGrowthGenerator

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

theorem closed_energy_coordinates (E : Point → ℝ)
    (hE : ∀ y, (1/200)*normSq y ≤ E y) (y : Point)
    (hy : E y ≤ 1/32000000) (i : Fin 4) : |y i| ≤ 1/400 := by
  have h := hE y
  have hi := coordinate_sq_le_normSq y i
  apply abs_le.mpr
  constructor <;> nlinarith only [h,hi,hy,sq_nonneg (y i+1/400),sq_nonneg (y i-1/400)]

theorem low_safe_geometry (z : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (x : Point)
    (he : lowEnergy (fun i => x i-pointOfState (lift sourceRates z) i) ≤ 1/32000000) :
    (99/100 ≤ x 2 ∧ x 2 ≤ 101/100) ∧ 10*x 2-x 1 < 0 := by
  have hy := closed_energy_coordinates lowEnergy lowEnergy_lower _ he
  have hy₁ := abs_le.mp (hy 1)
  have hy₂ := abs_le.mp (hy 2)
  change -(1/400) ≤ x 1-reducedB sourceRates z ∧
    x 1-reducedB sourceRates z ≤ 1/400 at hy₁
  change -(1/400) ≤ x 2-z ∧ x 2-z ≤ 1/400 at hy₂
  have hb := low_source_box z hz
  constructor
  · constructor <;> linarith only [hy₂.1,hy₂.2,hz.1,hz.2]
  · linarith only [hy₁.1,hy₂.2,hb.2.1.1,hz.2]

theorem high_safe_geometry (z : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (x : Point)
    (he : highEnergy (fun i => x i-pointOfState (lift sourceRates z) i) ≤ 1/32000000) :
    (297/100 ≤ x 2 ∧ x 2 ≤ 3) ∧ 0 < 10*x 2-x 1 := by
  have hy := closed_energy_coordinates highEnergy highEnergy_lower _ he
  have hy₁ := abs_le.mp (hy 1)
  have hy₂ := abs_le.mp (hy 2)
  change -(1/400) ≤ x 1-reducedB sourceRates z ∧
    x 1-reducedB sourceRates z ≤ 1/400 at hy₁
  change -(1/400) ≤ x 2-z ∧ x 2-z ≤ 1/400 at hy₂
  have hb := high_source_box z hz
  constructor
  · constructor <;> linarith only [hy₂.1,hy₂.2,hz.1,hz.2]
  · linarith only [hy₁.2,hy₂.1,hb.2.1.2,hz.1]

end ResourceLimitedCompetition
