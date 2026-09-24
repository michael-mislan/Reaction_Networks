import proofs.SmallCusp.Obstruction.CubicResidual000To000
import proofs.SmallCusp.Obstruction.CubicResidual001To001
import proofs.SmallCusp.Obstruction.CubicResidual002To005
import proofs.SmallCusp.Obstruction.CubicResidual006To015
import proofs.SmallCusp.Obstruction.CubicResidual016To025
import proofs.SmallCusp.Obstruction.CubicResidual026To035
import proofs.SmallCusp.Obstruction.CubicResidual036To045
import proofs.SmallCusp.Obstruction.CubicResidual046To055
import proofs.SmallCusp.Obstruction.CubicResidual056To065
import proofs.SmallCusp.Obstruction.CubicResidual066To075
import proofs.SmallCusp.Obstruction.CubicResidual076To085
import proofs.SmallCusp.Obstruction.CubicResidual086To095
import proofs.SmallCusp.Obstruction.CubicResidual096To105
import proofs.SmallCusp.Obstruction.CubicResidual106To115
import proofs.SmallCusp.Obstruction.CubicResidual116To125
import proofs.SmallCusp.Obstruction.CubicResidual126To135
import proofs.SmallCusp.Obstruction.CubicResidual136To139

namespace SmallCusp

/-- A residual cubic obstruction packaged with its source network.  The finite
list below records coefficient instances of the common four-chart ideal
mechanism; the proof field, rather than the list membership, carries the
mathematical obstruction. -/
structure CubicResidualRecord where
  network : CodedBimolNetwork
  excludesCusp : ¬ AdmitsTransverseCusp network.toNetwork

def cubicResidualLayerRecords : List CubicResidualRecord := [
  ⟨cubicResidualNetwork0, cubicResidualNetwork0_noCusp⟩,
  ⟨cubicResidualNetwork1, cubicResidualNetwork1_noCusp⟩,
  ⟨cubicResidualNetwork2, cubicResidualNetwork2_noCusp⟩,
  ⟨cubicResidualNetwork3, cubicResidualNetwork3_noCusp⟩,
  ⟨cubicResidualNetwork4, cubicResidualNetwork4_noCusp⟩,
  ⟨cubicResidualNetwork5, cubicResidualNetwork5_noCusp⟩,
  ⟨cubicResidualNetwork6, cubicResidualNetwork6_noCusp⟩,
  ⟨cubicResidualNetwork7, cubicResidualNetwork7_noCusp⟩,
  ⟨cubicResidualNetwork8, cubicResidualNetwork8_noCusp⟩,
  ⟨cubicResidualNetwork9, cubicResidualNetwork9_noCusp⟩,
  ⟨cubicResidualNetwork10, cubicResidualNetwork10_noCusp⟩,
  ⟨cubicResidualNetwork11, cubicResidualNetwork11_noCusp⟩,
  ⟨cubicResidualNetwork12, cubicResidualNetwork12_noCusp⟩,
  ⟨cubicResidualNetwork13, cubicResidualNetwork13_noCusp⟩,
  ⟨cubicResidualNetwork14, cubicResidualNetwork14_noCusp⟩,
  ⟨cubicResidualNetwork15, cubicResidualNetwork15_noCusp⟩,
  ⟨cubicResidualNetwork16, cubicResidualNetwork16_noCusp⟩,
  ⟨cubicResidualNetwork17, cubicResidualNetwork17_noCusp⟩,
  ⟨cubicResidualNetwork18, cubicResidualNetwork18_noCusp⟩,
  ⟨cubicResidualNetwork19, cubicResidualNetwork19_noCusp⟩,
  ⟨cubicResidualNetwork20, cubicResidualNetwork20_noCusp⟩,
  ⟨cubicResidualNetwork21, cubicResidualNetwork21_noCusp⟩,
  ⟨cubicResidualNetwork22, cubicResidualNetwork22_noCusp⟩,
  ⟨cubicResidualNetwork23, cubicResidualNetwork23_noCusp⟩,
  ⟨cubicResidualNetwork24, cubicResidualNetwork24_noCusp⟩,
  ⟨cubicResidualNetwork25, cubicResidualNetwork25_noCusp⟩,
  ⟨cubicResidualNetwork26, cubicResidualNetwork26_noCusp⟩,
  ⟨cubicResidualNetwork27, cubicResidualNetwork27_noCusp⟩,
  ⟨cubicResidualNetwork28, cubicResidualNetwork28_noCusp⟩,
  ⟨cubicResidualNetwork29, cubicResidualNetwork29_noCusp⟩,
  ⟨cubicResidualNetwork30, cubicResidualNetwork30_noCusp⟩,
  ⟨cubicResidualNetwork31, cubicResidualNetwork31_noCusp⟩,
  ⟨cubicResidualNetwork32, cubicResidualNetwork32_noCusp⟩,
  ⟨cubicResidualNetwork33, cubicResidualNetwork33_noCusp⟩,
  ⟨cubicResidualNetwork34, cubicResidualNetwork34_noCusp⟩,
  ⟨cubicResidualNetwork35, cubicResidualNetwork35_noCusp⟩,
  ⟨cubicResidualNetwork36, cubicResidualNetwork36_noCusp⟩,
  ⟨cubicResidualNetwork37, cubicResidualNetwork37_noCusp⟩,
  ⟨cubicResidualNetwork38, cubicResidualNetwork38_noCusp⟩,
  ⟨cubicResidualNetwork39, cubicResidualNetwork39_noCusp⟩,
  ⟨cubicResidualNetwork40, cubicResidualNetwork40_noCusp⟩,
  ⟨cubicResidualNetwork41, cubicResidualNetwork41_noCusp⟩,
  ⟨cubicResidualNetwork42, cubicResidualNetwork42_noCusp⟩,
  ⟨cubicResidualNetwork43, cubicResidualNetwork43_noCusp⟩,
  ⟨cubicResidualNetwork44, cubicResidualNetwork44_noCusp⟩,
  ⟨cubicResidualNetwork45, cubicResidualNetwork45_noCusp⟩,
  ⟨cubicResidualNetwork46, cubicResidualNetwork46_noCusp⟩,
  ⟨cubicResidualNetwork47, cubicResidualNetwork47_noCusp⟩,
  ⟨cubicResidualNetwork48, cubicResidualNetwork48_noCusp⟩,
  ⟨cubicResidualNetwork49, cubicResidualNetwork49_noCusp⟩,
  ⟨cubicResidualNetwork50, cubicResidualNetwork50_noCusp⟩,
  ⟨cubicResidualNetwork51, cubicResidualNetwork51_noCusp⟩,
  ⟨cubicResidualNetwork52, cubicResidualNetwork52_noCusp⟩,
  ⟨cubicResidualNetwork53, cubicResidualNetwork53_noCusp⟩,
  ⟨cubicResidualNetwork54, cubicResidualNetwork54_noCusp⟩,
  ⟨cubicResidualNetwork55, cubicResidualNetwork55_noCusp⟩,
  ⟨cubicResidualNetwork56, cubicResidualNetwork56_noCusp⟩,
  ⟨cubicResidualNetwork57, cubicResidualNetwork57_noCusp⟩,
  ⟨cubicResidualNetwork58, cubicResidualNetwork58_noCusp⟩,
  ⟨cubicResidualNetwork59, cubicResidualNetwork59_noCusp⟩,
  ⟨cubicResidualNetwork60, cubicResidualNetwork60_noCusp⟩,
  ⟨cubicResidualNetwork61, cubicResidualNetwork61_noCusp⟩,
  ⟨cubicResidualNetwork62, cubicResidualNetwork62_noCusp⟩,
  ⟨cubicResidualNetwork63, cubicResidualNetwork63_noCusp⟩,
  ⟨cubicResidualNetwork64, cubicResidualNetwork64_noCusp⟩,
  ⟨cubicResidualNetwork65, cubicResidualNetwork65_noCusp⟩,
  ⟨cubicResidualNetwork66, cubicResidualNetwork66_noCusp⟩,
  ⟨cubicResidualNetwork67, cubicResidualNetwork67_noCusp⟩,
  ⟨cubicResidualNetwork68, cubicResidualNetwork68_noCusp⟩,
  ⟨cubicResidualNetwork69, cubicResidualNetwork69_noCusp⟩,
  ⟨cubicResidualNetwork70, cubicResidualNetwork70_noCusp⟩,
  ⟨cubicResidualNetwork71, cubicResidualNetwork71_noCusp⟩,
  ⟨cubicResidualNetwork72, cubicResidualNetwork72_noCusp⟩,
  ⟨cubicResidualNetwork73, cubicResidualNetwork73_noCusp⟩,
  ⟨cubicResidualNetwork74, cubicResidualNetwork74_noCusp⟩,
  ⟨cubicResidualNetwork75, cubicResidualNetwork75_noCusp⟩,
  ⟨cubicResidualNetwork76, cubicResidualNetwork76_noCusp⟩,
  ⟨cubicResidualNetwork77, cubicResidualNetwork77_noCusp⟩,
  ⟨cubicResidualNetwork78, cubicResidualNetwork78_noCusp⟩,
  ⟨cubicResidualNetwork79, cubicResidualNetwork79_noCusp⟩,
  ⟨cubicResidualNetwork80, cubicResidualNetwork80_noCusp⟩,
  ⟨cubicResidualNetwork81, cubicResidualNetwork81_noCusp⟩,
  ⟨cubicResidualNetwork82, cubicResidualNetwork82_noCusp⟩,
  ⟨cubicResidualNetwork83, cubicResidualNetwork83_noCusp⟩,
  ⟨cubicResidualNetwork84, cubicResidualNetwork84_noCusp⟩,
  ⟨cubicResidualNetwork85, cubicResidualNetwork85_noCusp⟩,
  ⟨cubicResidualNetwork86, cubicResidualNetwork86_noCusp⟩,
  ⟨cubicResidualNetwork87, cubicResidualNetwork87_noCusp⟩,
  ⟨cubicResidualNetwork88, cubicResidualNetwork88_noCusp⟩,
  ⟨cubicResidualNetwork89, cubicResidualNetwork89_noCusp⟩,
  ⟨cubicResidualNetwork90, cubicResidualNetwork90_noCusp⟩,
  ⟨cubicResidualNetwork91, cubicResidualNetwork91_noCusp⟩,
  ⟨cubicResidualNetwork92, cubicResidualNetwork92_noCusp⟩,
  ⟨cubicResidualNetwork93, cubicResidualNetwork93_noCusp⟩,
  ⟨cubicResidualNetwork94, cubicResidualNetwork94_noCusp⟩,
  ⟨cubicResidualNetwork95, cubicResidualNetwork95_noCusp⟩,
  ⟨cubicResidualNetwork96, cubicResidualNetwork96_noCusp⟩,
  ⟨cubicResidualNetwork97, cubicResidualNetwork97_noCusp⟩,
  ⟨cubicResidualNetwork98, cubicResidualNetwork98_noCusp⟩,
  ⟨cubicResidualNetwork99, cubicResidualNetwork99_noCusp⟩,
  ⟨cubicResidualNetwork100, cubicResidualNetwork100_noCusp⟩,
  ⟨cubicResidualNetwork101, cubicResidualNetwork101_noCusp⟩,
  ⟨cubicResidualNetwork102, cubicResidualNetwork102_noCusp⟩,
  ⟨cubicResidualNetwork103, cubicResidualNetwork103_noCusp⟩,
  ⟨cubicResidualNetwork104, cubicResidualNetwork104_noCusp⟩,
  ⟨cubicResidualNetwork105, cubicResidualNetwork105_noCusp⟩,
  ⟨cubicResidualNetwork106, cubicResidualNetwork106_noCusp⟩,
  ⟨cubicResidualNetwork107, cubicResidualNetwork107_noCusp⟩,
  ⟨cubicResidualNetwork108, cubicResidualNetwork108_noCusp⟩,
  ⟨cubicResidualNetwork109, cubicResidualNetwork109_noCusp⟩,
  ⟨cubicResidualNetwork110, cubicResidualNetwork110_noCusp⟩,
  ⟨cubicResidualNetwork111, cubicResidualNetwork111_noCusp⟩,
  ⟨cubicResidualNetwork112, cubicResidualNetwork112_noCusp⟩,
  ⟨cubicResidualNetwork113, cubicResidualNetwork113_noCusp⟩,
  ⟨cubicResidualNetwork114, cubicResidualNetwork114_noCusp⟩,
  ⟨cubicResidualNetwork115, cubicResidualNetwork115_noCusp⟩,
  ⟨cubicResidualNetwork116, cubicResidualNetwork116_noCusp⟩,
  ⟨cubicResidualNetwork117, cubicResidualNetwork117_noCusp⟩,
  ⟨cubicResidualNetwork118, cubicResidualNetwork118_noCusp⟩,
  ⟨cubicResidualNetwork119, cubicResidualNetwork119_noCusp⟩,
  ⟨cubicResidualNetwork120, cubicResidualNetwork120_noCusp⟩,
  ⟨cubicResidualNetwork121, cubicResidualNetwork121_noCusp⟩,
  ⟨cubicResidualNetwork122, cubicResidualNetwork122_noCusp⟩,
  ⟨cubicResidualNetwork123, cubicResidualNetwork123_noCusp⟩,
  ⟨cubicResidualNetwork124, cubicResidualNetwork124_noCusp⟩,
  ⟨cubicResidualNetwork125, cubicResidualNetwork125_noCusp⟩,
  ⟨cubicResidualNetwork126, cubicResidualNetwork126_noCusp⟩,
  ⟨cubicResidualNetwork127, cubicResidualNetwork127_noCusp⟩,
  ⟨cubicResidualNetwork128, cubicResidualNetwork128_noCusp⟩,
  ⟨cubicResidualNetwork129, cubicResidualNetwork129_noCusp⟩,
  ⟨cubicResidualNetwork130, cubicResidualNetwork130_noCusp⟩,
  ⟨cubicResidualNetwork131, cubicResidualNetwork131_noCusp⟩,
  ⟨cubicResidualNetwork132, cubicResidualNetwork132_noCusp⟩,
  ⟨cubicResidualNetwork133, cubicResidualNetwork133_noCusp⟩,
  ⟨cubicResidualNetwork134, cubicResidualNetwork134_noCusp⟩,
  ⟨cubicResidualNetwork135, cubicResidualNetwork135_noCusp⟩,
  ⟨cubicResidualNetwork136, cubicResidualNetwork136_noCusp⟩,
  ⟨cubicResidualNetwork137, cubicResidualNetwork137_noCusp⟩,
  ⟨cubicResidualNetwork138, cubicResidualNetwork138_noCusp⟩,
  ⟨cubicResidualNetwork139, cubicResidualNetwork139_noCusp⟩
]

theorem cubicResidualLayerRecords_length :
    cubicResidualLayerRecords.length = 140 := by
  native_decide

def IsCubicResidualLayerNetwork (C : CodedBimolNetwork) : Prop :=
  ∃ R ∈ cubicResidualLayerRecords, C.reaction = R.network.reaction

private theorem cubicResidualNetwork_eq_of_reaction_eq
    (C D : CodedBimolNetwork) (h : C.reaction = D.reaction) :
    C.toNetwork = D.toNetwork := by
  cases C with
  | mk reaction noSelf injective =>
    cases D with
    | mk reaction' noSelf' injective' =>
      simp only at h
      subst reaction'
      rfl

theorem isCubicResidualLayerNetwork_excludes_cusp (C : CodedBimolNetwork)
    (hC : IsCubicResidualLayerNetwork C) :
    ¬ AdmitsTransverseCusp C.toNetwork := by
  rcases hC with ⟨R, hR, hreactions⟩
  have hnetwork : C.toNetwork = R.network.toNetwork :=
    cubicResidualNetwork_eq_of_reaction_eq C R.network hreactions
  rw [hnetwork]
  exact R.excludesCusp

end SmallCusp
