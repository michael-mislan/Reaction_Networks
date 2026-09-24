import proofs.SmallCusp.Cusp.PositiveCusp00
import proofs.SmallCusp.Cusp.PositiveCusp01
import proofs.SmallCusp.Cusp.PositiveCusp02
import proofs.SmallCusp.Cusp.PositiveCusp03
import proofs.SmallCusp.Cusp.PositiveCusp04
import proofs.SmallCusp.Cusp.PositiveCusp05
import proofs.SmallCusp.Cusp.PositiveCusp06
import proofs.SmallCusp.Cusp.PositiveCusp07
import proofs.SmallCusp.Cusp.PositiveCusp08
import proofs.SmallCusp.Cusp.PositiveCusp09
import proofs.SmallCusp.Cusp.PositiveCusp10
import proofs.SmallCusp.Cusp.PositiveCusp11
import proofs.SmallCusp.Cusp.PositiveCusp12
import proofs.SmallCusp.Cusp.PositiveCusp13
import proofs.SmallCusp.Cusp.PositiveCusp14
import proofs.SmallCusp.Cusp.PositiveCusp15
import proofs.SmallCusp.Cusp.PositiveCusp16
import proofs.SmallCusp.Cusp.PositiveCusp17
import proofs.SmallCusp.Cusp.PositiveCusp18
import proofs.SmallCusp.Cusp.PositiveCusp19
import proofs.SmallCusp.Cusp.PositiveCusp20
import proofs.SmallCusp.Cusp.PositiveCusp21
import proofs.SmallCusp.Cusp.PositiveCusp22
import proofs.SmallCusp.Cusp.PositiveCusp23
import proofs.SmallCusp.Cusp.PositiveCusp24
import proofs.SmallCusp.Cusp.PositiveCusp25
import proofs.SmallCusp.Cusp.PositiveCusp26
import proofs.SmallCusp.Cusp.PositiveCusp27
import proofs.SmallCusp.Cusp.PositiveCusp28
import proofs.SmallCusp.Cusp.PositiveCusp29
import proofs.SmallCusp.Cusp.PositiveCusp30
import proofs.SmallCusp.Cusp.PositiveCusp31
import proofs.SmallCusp.Cusp.PositiveCusp32
import proofs.SmallCusp.Cusp.PositiveCusp33
import proofs.SmallCusp.Cusp.PositiveCusp34
import proofs.SmallCusp.Cusp.PositiveCusp35
import proofs.SmallCusp.Cusp.PositiveCusp36
import proofs.SmallCusp.Cusp.PositiveCusp37
import proofs.SmallCusp.Cusp.PositiveCusp38
import proofs.SmallCusp.Cusp.PositiveCusp39
import proofs.SmallCusp.Cusp.PositiveCusp40
import proofs.SmallCusp.Cusp.PositiveCusp41
import proofs.SmallCusp.Cusp.PositiveCusp42
import proofs.SmallCusp.Cusp.PositiveCusp43
import proofs.SmallCusp.Cusp.PositiveCusp44
import proofs.SmallCusp.Cusp.PositiveCusp45
import proofs.SmallCusp.Cusp.PositiveCusp46
import proofs.SmallCusp.Cusp.PositiveCusp47
import proofs.SmallCusp.Cusp.PositiveCusp48
import proofs.SmallCusp.Cusp.PositiveCusp49
import proofs.SmallCusp.Cusp.PositiveCusp50
import proofs.SmallCusp.Cusp.PositiveCusp51

set_option maxHeartbeats 800000

namespace SmallCusp

/- The finite source payload for the uniform triangular cusp constructor. -/
def bimolecularCuspClasses : List CodedBimolNetwork := [
  positiveCusp0,
  positiveCusp1,
  positiveCusp2,
  positiveCusp3,
  positiveCusp4,
  positiveCusp5,
  positiveCusp6,
  positiveCusp7,
  positiveCusp8,
  positiveCusp9,
  positiveCusp10,
  positiveCusp11,
  positiveCusp12,
  positiveCusp13,
  positiveCusp14,
  positiveCusp15,
  positiveCusp16,
  positiveCusp17,
  positiveCusp18,
  positiveCusp19,
  positiveCusp20,
  positiveCusp21,
  positiveCusp22,
  positiveCusp23,
  positiveCusp24,
  positiveCusp25,
  positiveCusp26,
  positiveCusp27,
  positiveCusp28,
  positiveCusp29,
  positiveCusp30,
  positiveCusp31,
  positiveCusp32,
  positiveCusp33,
  positiveCusp34,
  positiveCusp35,
  positiveCusp36,
  positiveCusp37,
  positiveCusp38,
  positiveCusp39,
  positiveCusp40,
  positiveCusp41,
  positiveCusp42,
  positiveCusp43,
  positiveCusp44,
  positiveCusp45,
  positiveCusp46,
  positiveCusp47,
  positiveCusp48,
  positiveCusp49,
  positiveCusp50,
  positiveCusp51]

theorem bimolecularCuspClass_admits {Q : CodedBimolNetwork}
    (h : Q ∈ bimolecularCuspClasses) : AdmitsTransverseCusp Q.toNetwork := by
  simp only [bimolecularCuspClasses, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51
  all_goals subst Q
  all_goals first
    | exact positiveCusp0_admitsTransverseCusp
    | exact positiveCusp1_admitsTransverseCusp
    | exact positiveCusp2_admitsTransverseCusp
    | exact positiveCusp3_admitsTransverseCusp
    | exact positiveCusp4_admitsTransverseCusp
    | exact positiveCusp5_admitsTransverseCusp
    | exact positiveCusp6_admitsTransverseCusp
    | exact positiveCusp7_admitsTransverseCusp
    | exact positiveCusp8_admitsTransverseCusp
    | exact positiveCusp9_admitsTransverseCusp
    | exact positiveCusp10_admitsTransverseCusp
    | exact positiveCusp11_admitsTransverseCusp
    | exact positiveCusp12_admitsTransverseCusp
    | exact positiveCusp13_admitsTransverseCusp
    | exact positiveCusp14_admitsTransverseCusp
    | exact positiveCusp15_admitsTransverseCusp
    | exact positiveCusp16_admitsTransverseCusp
    | exact positiveCusp17_admitsTransverseCusp
    | exact positiveCusp18_admitsTransverseCusp
    | exact positiveCusp19_admitsTransverseCusp
    | exact positiveCusp20_admitsTransverseCusp
    | exact positiveCusp21_admitsTransverseCusp
    | exact positiveCusp22_admitsTransverseCusp
    | exact positiveCusp23_admitsTransverseCusp
    | exact positiveCusp24_admitsTransverseCusp
    | exact positiveCusp25_admitsTransverseCusp
    | exact positiveCusp26_admitsTransverseCusp
    | exact positiveCusp27_admitsTransverseCusp
    | exact positiveCusp28_admitsTransverseCusp
    | exact positiveCusp29_admitsTransverseCusp
    | exact positiveCusp30_admitsTransverseCusp
    | exact positiveCusp31_admitsTransverseCusp
    | exact positiveCusp32_admitsTransverseCusp
    | exact positiveCusp33_admitsTransverseCusp
    | exact positiveCusp34_admitsTransverseCusp
    | exact positiveCusp35_admitsTransverseCusp
    | exact positiveCusp36_admitsTransverseCusp
    | exact positiveCusp37_admitsTransverseCusp
    | exact positiveCusp38_admitsTransverseCusp
    | exact positiveCusp39_admitsTransverseCusp
    | exact positiveCusp40_admitsTransverseCusp
    | exact positiveCusp41_admitsTransverseCusp
    | exact positiveCusp42_admitsTransverseCusp
    | exact positiveCusp43_admitsTransverseCusp
    | exact positiveCusp44_admitsTransverseCusp
    | exact positiveCusp45_admitsTransverseCusp
    | exact positiveCusp46_admitsTransverseCusp
    | exact positiveCusp47_admitsTransverseCusp
    | exact positiveCusp48_admitsTransverseCusp
    | exact positiveCusp49_admitsTransverseCusp
    | exact positiveCusp50_admitsTransverseCusp
    | exact positiveCusp51_admitsTransverseCusp

theorem bimolecularCuspClasses_length :
    bimolecularCuspClasses.length = 52 := by
  native_decide

end SmallCusp
