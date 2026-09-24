import proofs.RAFBiochemicalInterventions.ParentSource
import proofs.RAFBiochemicalInterventions.LiteralSupport

namespace RAFBiochemicalLiteral.ParentIntervention
open ParentSource
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
def supportR01209 : List Row := [⟨257, 161, [1, 2], [5, 6], catalyst68⟩, ⟨534, 351, [20, 63], [9, 2643], catalyst139⟩, ⟨9192, 6000, [56], [5509], catalyst393⟩, ⟨538, 354, [20, 2643], [63, 699], catalyst140⟩, ⟨2535, 1647, [5, 28], [4, 26, 75], catalyst151⟩, ⟨9190, 5998, [5], [5730], catalyst393⟩, ⟨1313, 822, [4, 75, 699], [5, 2191], catalyst147⟩, ⟨7835, 5105, [2191], [0, 132], catalyst172⟩, ⟨2377, 1542, [4, 12, 75, 132], [0, 5, 168], catalyst145⟩]
theorem checkedR01209 : checkSupport (remaining rows (restore cut 5105)) food
    supportR01209 supportR01209 target = true := by decide +kernel
theorem restoredR01209 : Capable (remaining rows (restore cut 5105)) food target :=
  checked_support _ _ _ _ _ checkedR01209
def supportR01210 : List Row := [⟨885, 557, [2, 123], [3, 62, 75], catalyst150⟩, ⟨8766, 5699, [1, 8, 31], [6, 7, 22], catalyst381⟩, ⟨9192, 6000, [56], [5509], catalyst393⟩, ⟨9227, 6035, [446], [5507], catalyst393⟩, ⟨8970, 5835, [1, 22, 257], [6, 7, 78], catalyst290⟩, ⟨9188, 5996, [3], [5730], catalyst393⟩, ⟨3434, 2239, [22, 78], [8, 9, 287], catalyst203⟩, ⟨1096, 692, [3, 75, 287], [2, 867], catalyst151⟩, ⟨7672, 5002, [867], [0, 683], catalyst158⟩, ⟨2006, 1282, [3, 130, 683], [2, 127, 129], catalyst145⟩, ⟨8610, 5583, [127], [509], catalyst299⟩, ⟨1697, 1069, [3, 9, 75, 509], [2, 8, 132], catalyst153⟩, ⟨2368, 1536, [3, 12, 75, 132], [0, 2, 168], catalyst145⟩]
theorem checkedR01210 : checkSupport (remaining rows (restore cut 1069)) food
    supportR01210 supportR01210 target = true := by decide +kernel
theorem restoredR01210 : Capable (remaining rows (restore cut 1069)) food target :=
  checked_support _ _ _ _ _ checkedR01210
def supportR04441 : List Row := [⟨475, 314, [1, 20, 257], [6, 7, 33], catalyst124⟩, ⟨534, 351, [20, 63], [9, 2643], catalyst139⟩, ⟨8206, 5337, [12, 20, 255], [0, 92], catalyst362⟩, ⟨9187, 5995, [2], [5730], catalyst393⟩, ⟨540, 355, [20, 2643], [63, 3038], catalyst140⟩, ⟨7504, 4886, [31, 33], [147], catalyst155⟩, ⟨7720, 5033, [147], [0, 354], catalyst172⟩, ⟨7723, 5034, [0, 354], [270], catalyst172⟩, ⟨959, 601, [2, 270], [3, 9, 24, 75], catalyst152⟩, ⟨1181, 745, [3, 75, 3038], [2, 2316], catalyst147⟩, ⟨4738, 3064, [24, 92], [23, 733], catalyst257⟩, ⟨7836, 5106, [2316], [0, 132], catalyst172⟩, ⟨4763, 3077, [23, 132], [24, 168], catalyst257⟩]
theorem checkedR04441 : checkSupport (remaining rows (restore cut 5106)) food
    supportR04441 supportR04441 target = true := by decide +kernel
theorem restoredR04441 : Capable (remaining rows (restore cut 5106)) food target :=
  checked_support _ _ _ _ _ checkedR04441
def methionineSupport : List Row := [⟨4654, 3012, [17, 565], [68, 4601], catalyst240⟩]
theorem methionine_checked : checkSupport (remaining rows cut) food
    methionineSupport methionineSupport 68 = true := by decide +kernel
theorem methionine_preserved : Capable (remaining rows cut) food 68 :=
  checked_support _ _ _ _ _ methionine_checked

theorem valine_eliminated : ¬ Capable (remaining rows cut) food target :=
  not_capable_of_not_generated (by
    have h := ParentSource.valine_absent
    unfold ParentSource.TargetAbsent at h
    exact h)

theorem valine_cut_minimal : MinimalCut rows food target cut := by
  apply minimal_cut_of_restorations rows food target cut valine_eliminated
  intro a ha
  simp only [cut, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h
  · subst a; exact restoredR01209
  · subst a; exact restoredR01210
  · subst a; exact restoredR04441

end RAFBiochemicalLiteral.ParentIntervention
