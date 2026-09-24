import proofs.AssayInformation.GroupedPolynomial

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000
noncomputable section
namespace AssayInformation

def upperA : ℝ := (58127977432913971291/1119213810000000000000)
def upperB : ℝ := (4460289996897543441049/33496650000000000000)
def upperD : ℝ := (39482871378014276053/292436718750000000)
def upperE : ℝ := (2097477539856377942137/16499587500000000000)
def upperG : ℝ := (1174288464444238226307/9390001562500000000)
theorem upper_poly_negative (x : ℝ) (hx : x ∈ Set.Icc 0 (9901/10000)) :
    signedPoly upperA upperB upperD upperE upperG x < 0 := by
  apply signedPoly_negative_right upperA upperB upperD upperE upperG (9901/10000)
  · norm_num
  · norm_num [upperA,upperB,upperD,upperE,upperG]
  · norm_num [upperA,upperB,upperD,upperE,upperG]
  · norm_num [upperA,upperB,upperD,upperE,upperG]
  · norm_num [upperA,upperB,upperD,upperE,upperG]
  · norm_num [signedPoly,grouped,upperA,upperB,upperD,upperE,upperG]
  · exact hx

def lowerA : ℝ := (3632998589564415917/69950863125000000000)
def lowerB : ℝ := (278768124723573721663/2093540625000000000)
def lowerD : ℝ := (631725942233871676019/4678987500000000000)
def lowerE : ℝ := (131092346239129121119/1031224218750000000)
def lowerG : ℝ := (18788615431332200694261/150240025000000000000)
theorem lower_poly_cell0 (x : ℝ) (hx : x ∈ Set.Icc (124/125) (497/500)) :
    0 < signedPoly lowerA lowerB lowerD lowerE lowerG x := by
  apply signedPoly_positive_cell lowerA lowerB lowerD lowerE lowerG (124/125) (497/500)
  · norm_num
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [grouped,lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [grouped,lowerA,lowerB,lowerD,lowerE,lowerG]
  · exact hx

theorem lower_poly_cell1 (x : ℝ) (hx : x ∈ Set.Icc (497/500) (249/250)) :
    0 < signedPoly lowerA lowerB lowerD lowerE lowerG x := by
  apply signedPoly_positive_cell lowerA lowerB lowerD lowerE lowerG (497/500) (249/250)
  · norm_num
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [grouped,lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [grouped,lowerA,lowerB,lowerD,lowerE,lowerG]
  · exact hx

theorem lower_poly_cell2 (x : ℝ) (hx : x ∈ Set.Icc (249/250) (499/500)) :
    0 < signedPoly lowerA lowerB lowerD lowerE lowerG x := by
  apply signedPoly_positive_cell lowerA lowerB lowerD lowerE lowerG (249/250) (499/500)
  · norm_num
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [grouped,lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [grouped,lowerA,lowerB,lowerD,lowerE,lowerG]
  · exact hx

theorem lower_poly_cell3 (x : ℝ) (hx : x ∈ Set.Icc (499/500) (1/1)) :
    0 < signedPoly lowerA lowerB lowerD lowerE lowerG x := by
  apply signedPoly_positive_cell lowerA lowerB lowerD lowerE lowerG (499/500) (1/1)
  · norm_num
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [grouped,lowerA,lowerB,lowerD,lowerE,lowerG]
  · norm_num [grouped,lowerA,lowerB,lowerD,lowerE,lowerG]
  · exact hx

theorem lower_poly_positive (x : ℝ) (hx : x ∈ Set.Icc (124/125) 1) :
    0 < signedPoly lowerA lowerB lowerD lowerE lowerG x := by
  by_cases h0 : x ≤ 497/500
  · exact lower_poly_cell0 x ⟨hx.1,h0⟩
  by_cases h1 : x ≤ 249/250
  · exact lower_poly_cell1 x ⟨by linarith,h1⟩
  by_cases h2 : x ≤ 499/500
  · exact lower_poly_cell2 x ⟨by linarith,h2⟩
  exact lower_poly_cell3 x ⟨by linarith,by simpa using hx.2⟩

end AssayInformation
