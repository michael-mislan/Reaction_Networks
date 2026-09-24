import proofs.SmallCusp.Obstruction.ConicDetC00
import proofs.SmallCusp.Obstruction.ConicDetC01
import proofs.SmallCusp.Obstruction.ConicDetC02
import proofs.SmallCusp.Obstruction.ConicDetC03
import proofs.SmallCusp.Obstruction.ConicDetC04
import proofs.SmallCusp.Obstruction.ConicDetC05
import proofs.SmallCusp.Obstruction.ConicDetC06
import proofs.SmallCusp.Obstruction.ConicDetC07
import proofs.SmallCusp.Obstruction.ConicDetC08
import proofs.SmallCusp.Obstruction.ConicDetC09
import proofs.SmallCusp.Obstruction.ConicDetC10
import proofs.SmallCusp.Obstruction.ConicDetC11
import proofs.SmallCusp.Obstruction.ConicDetC12
import proofs.SmallCusp.Obstruction.ConicDetC13
import proofs.SmallCusp.Obstruction.ConicDetC14
import proofs.SmallCusp.Obstruction.ConicDetC15
import proofs.SmallCusp.Obstruction.ConicDetC16
import proofs.SmallCusp.Obstruction.ConicDetC17
import proofs.SmallCusp.Obstruction.ConicDetC18
import proofs.SmallCusp.Obstruction.ConicDetC19
import proofs.SmallCusp.Obstruction.ConicDetC20
import proofs.SmallCusp.Obstruction.ConicDetC21
import proofs.SmallCusp.Obstruction.ConicDetC22A
import proofs.SmallCusp.Obstruction.ConicDetC22B
import proofs.SmallCusp.Obstruction.ConicDetC23
import proofs.SmallCusp.Obstruction.ConicDetC24
import proofs.SmallCusp.Obstruction.ConicDetC25
import proofs.SmallCusp.Obstruction.ConicDetC26
import proofs.SmallCusp.Obstruction.ConicDetC27
import proofs.SmallCusp.Obstruction.ConicDetC28
import proofs.SmallCusp.Obstruction.ConicDetC29
import proofs.SmallCusp.Obstruction.ConicDetC30
import proofs.SmallCusp.Obstruction.ConicDetC31
import proofs.SmallCusp.Obstruction.ConicDetC32A
import proofs.SmallCusp.Obstruction.ConicDetC32B
import proofs.SmallCusp.Obstruction.ConicDetC33
import proofs.SmallCusp.Obstruction.ConicDetC34
import proofs.SmallCusp.Obstruction.ConicDetC35

namespace SmallCusp

def conicDeterminantLayerRecords : List RationalConicRecord :=
  conicDetC00 ++ conicDetC01 ++ conicDetC02 ++ conicDetC03 ++
  conicDetC04 ++ conicDetC05 ++ conicDetC06 ++ conicDetC07 ++
  conicDetC08 ++ conicDetC09 ++ conicDetC10 ++ conicDetC11 ++
  conicDetC12 ++ conicDetC13 ++ conicDetC14 ++ conicDetC15 ++
  conicDetC16 ++ conicDetC17 ++ conicDetC18 ++ conicDetC19 ++
  conicDetC20 ++ conicDetC21 ++ conicDetC22A ++ conicDetC22B ++
  conicDetC23 ++ conicDetC24 ++ conicDetC25 ++ conicDetC26 ++
  conicDetC27 ++ conicDetC28 ++ conicDetC29 ++ conicDetC30 ++
  conicDetC31 ++ conicDetC32A ++ conicDetC32B ++ conicDetC33 ++
  conicDetC34 ++ conicDetC35

theorem conicDeterminantLayerRecords_checked :
    conicDeterminantLayerRecords.all RationalConicRecord.check = true := by
  simp [conicDeterminantLayerRecords, conicDetC00_checked, conicDetC01_checked,
    conicDetC02_checked, conicDetC03_checked, conicDetC04_checked,
    conicDetC05_checked, conicDetC06_checked, conicDetC07_checked,
    conicDetC08_checked, conicDetC09_checked, conicDetC10_checked,
    conicDetC11_checked, conicDetC12_checked, conicDetC13_checked,
    conicDetC14_checked, conicDetC15_checked, conicDetC16_checked,
    conicDetC17_checked, conicDetC18_checked, conicDetC19_checked,
    conicDetC20_checked, conicDetC21_checked, conicDetC22A_checked,
    conicDetC22B_checked, conicDetC23_checked, conicDetC24_checked,
    conicDetC25_checked, conicDetC26_checked, conicDetC27_checked,
    conicDetC28_checked, conicDetC29_checked, conicDetC30_checked,
    conicDetC31_checked, conicDetC32A_checked, conicDetC32B_checked,
    conicDetC33_checked, conicDetC34_checked, conicDetC35_checked]

theorem conicDeterminantLayerRecords_length :
    conicDeterminantLayerRecords.length = 9063 := by
  native_decide

def IsConicDeterminantLayerNetwork (C : CodedBimolNetwork) : Prop :=
  ∃ R ∈ conicDeterminantLayerRecords, C.reaction = R.network.reaction

private theorem codedNetwork_toNetwork_eq_of_reaction_eq
    (C D : CodedBimolNetwork) (h : C.reaction = D.reaction) :
    C.toNetwork = D.toNetwork := by
  cases C with
  | mk reaction noSelf injective =>
    cases D with
    | mk reaction' noSelf' injective' =>
      simp only at h
      subst reaction'
      rfl

theorem isConicDeterminantLayerNetwork_excludes_cusp
    (C : CodedBimolNetwork) (hC : IsConicDeterminantLayerNetwork C) :
    ¬ AdmitsTransverseCusp C.toNetwork := by
  rcases hC with ⟨R, hR, hreactions⟩
  have hvalid : R.Valid :=
    RationalConicRecord.valid_of_mem_of_all_checked
      conicDeterminantLayerRecords conicDeterminantLayerRecords_checked hR
  have hnetwork : C.toNetwork = R.network.toNetwork :=
    codedNetwork_toNetwork_eq_of_reaction_eq C R.network hreactions
  rw [hnetwork]
  exact R.excludes_cusp hvalid

end SmallCusp
