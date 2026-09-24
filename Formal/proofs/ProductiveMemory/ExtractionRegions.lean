import proofs.ProductiveMemory.ExtractionReturn

namespace ProductiveMemory
open FiniteCopy Set
noncomputable section
set_option Elab.async false

def outerLevel : ℝ := 1/32000000
def returnLevel : ℝ := outerLevel/2
def readyLevel : ℝ := outerLevel/16
def energyRegion (E : Point → ℝ) (s : Point) (level : ℝ) : Set Point :=
  {x | E (fun i => x i-s i) ≤ level}

theorem region_levels : 0 < readyLevel ∧ readyLevel < returnLevel ∧
    returnLevel < outerLevel := by norm_num [readyLevel,returnLevel,outerLevel]

theorem energy_controls_coordinates (E : Point → ℝ)
    (hlower : ∀ y, (1/200:ℝ)*normSq y ≤ E y) (s x : Point)
    (hx : x ∈ energyRegion E s outerLevel) : ∀ i, |x i-s i| ≤ 1/400 := by
  intro i
  have hc := coordinate_sq_le_normSq (fun j => x j-s j) i
  have he := hlower (fun j => x j-s j)
  change E (fun j => x j-s j) ≤ outerLevel at hx
  norm_num [outerLevel] at hx
  change (x i-s i)^2 ≤ _ at hc
  apply abs_le.mpr
  constructor <;> nlinarith only [hc,he,hx]

theorem low_outer_readout (rho z : ℝ) (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (x : Point) (hx : x ∈ energyRegion lowExtractionEnergy (lift rho z) outerLevel) :
    97/100 ≤ x 2 ∧ x 2 ≤ 1 := by
  have hh := abs_le.mp (energy_controls_coordinates lowExtractionEnergy
    lowExtractionEnergy_lower (lift rho z) x hx 2)
  norm_num [lift,Matrix.cons_val_two] at hh
  constructor <;> linarith [hz.1,hz.2]

theorem high_outer_readout (rho z : ℝ) (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (x : Point) (hx : x ∈ energyRegion highExtractionEnergy (lift rho z) outerLevel) :
    288/100 ≤ x 2 ∧ x 2 ≤ 3 := by
  have hh := abs_le.mp (energy_controls_coordinates highExtractionEnergy
    highExtractionEnergy_lower (lift rho z) x hx 2)
  norm_num [lift,Matrix.cons_val_two] at hh
  constructor <;> linarith [hz.1,hz.2]

theorem separated_outer_regions (rho lo hi : ℝ)
    (hl : lo ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hh : hi ∈ Icc (289014/100000:ℝ) (289017/100000)) :
    Disjoint (energyRegion lowExtractionEnergy (lift rho lo) outerLevel)
      (energyRegion highExtractionEnergy (lift rho hi) outerLevel) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hlow := low_outer_readout rho lo hl x hx
  have hhigh := high_outer_readout rho hi hh x hy
  linarith [hlow.2,hhigh.1]

theorem low_ready_center (rho z : ℝ) :
    lift rho z ∈ energyRegion lowExtractionEnergy (lift rho z) readyLevel := by
  norm_num [energyRegion,lowExtractionEnergy,lowExtractionPair,readyLevel,outerLevel]

theorem high_ready_center (rho z : ℝ) :
    lift rho z ∈ energyRegion highExtractionEnergy (lift rho z) readyLevel := by
  norm_num [energyRegion,highExtractionEnergy,highExtractionPair,readyLevel,outerLevel]

theorem lift_coordinate_upper (rho z : ℝ) (hz : z ∈ Icc 0 3)
    (ha : reducedA rho z ≤ 34) (hb : reducedB z ≤ 34) : ∀ i, lift rho z i ≤ 34 := by
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hz.2.trans (by norm_num)
  · change (16*z+2*z^2)/(2+1/10000:ℝ) ≤ 34
    norm_num
    nlinarith [hz.1,hz.2]

end
end ProductiveMemory
