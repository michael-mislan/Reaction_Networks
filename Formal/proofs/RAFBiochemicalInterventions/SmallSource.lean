import proofs.RAFBiochemicalInterventions.LiteralStructure
namespace RAFBiochemicalLiteral.SmallSource
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
def food : List Nat := [254, 9, 0, 5728, 5732, 5731, 7, 54, 5734, 5737, 266, 4531, 35, 161, 71, 4530, 3881, 65, 3834, 1018, 3302, 3882, 217, 991, 565, 564, 994, 12, 3142, 257, 75, 11, 21, 26, 28, 47, 82, 255, 31, 53, 20, 123, 56, 16, 63, 2, 2999, 446, 105, 4099, 1, 111, 48, 3914, 17, 5733, 95, 5739, 5738, 2201, 18, 3042, 860, 652, 8, 129, 130, 216]
def r0 : Row := ⟨534, 351, [20, 63], [9, 2643], (.either (.either (.either (.both (.atom 63) (.atom 266)) (.both (.atom 5729) (.atom 5728))) (.both (.atom 5509) (.atom 63))) (.both (.atom 63) (.atom 4099)))⟩
def r1 : Row := ⟨540, 355, [20, 2643], [63, 3038], (.either (.both (.atom 63) (.atom 266)) (.both (.atom 5729) (.atom 5728)))⟩
def r2 : Row := ⟨1181, 745, [3, 75, 3038], [2, 2316], (.both (.atom 266) (.atom 5730))⟩
def r3 : Row := ⟨1187, 750, [2, 60], [3, 75, 3673], (.atom 5730)⟩
def r4 : Row := ⟨4786, 3090, [20, 60], [38, 157], (.atom 16)⟩
def r5 : Row := ⟨4818, 3108, [38, 132], [20, 168], (.atom 16)⟩
def r6 : Row := ⟨7836, 5106, [2316], [0, 132], (.atom 5728)⟩
def r7 : Row := ⟨8111, 5273, [12, 20], [590], (.atom 16)⟩
def r8 : Row := ⟨8274, 5382, [590], [60], (.atom 16)⟩
def r9 : Row := ⟨9188, 5996, [3], [5730], (.atom 5734)⟩
def rows : List Row := [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9]
theorem only_seeds : ∀ r ∈ rows, (∀ x ∈ r.inputs, x ∈ food) → r = r0 ∨ r = r7 := by decide +kernel
theorem seed0_checked : checkSupport rows food [r0] [r0] 0 = true := by decide +kernel
theorem seed0_raf : RAF [r0] food := checked_raf _ _ _ _ _ seed0_checked
theorem seed7_checked : checkSupport rows food [r7] [r7] 0 = true := by decide +kernel
theorem seed7_raf : RAF [r7] food := checked_raf _ _ _ _ _ seed7_checked
theorem irreducible_catalogue (S : List Row) (hsub : Subrows S rows) :
    Irreducible S food ↔ SameRows S [r0] ∨ SameRows S [r7] :=
  catalogue_from_seeds rows food r0 r7 only_seeds seed0_raf seed7_raf S hsub
def order : List Row := [r0, r7, r1, r8, r3, r4, r2, r9, r6, r5]
theorem whole_checked : checkSupport rows food rows order 168 = true := by decide +kernel
theorem whole_raf : RAF rows food := checked_raf _ _ _ _ _ whole_checked
theorem valine_capable : Capable rows food 168 := checked_support _ _ _ _ _ whole_checked
def lower : List Row := [r0, r1, r4, r7, r8]
def lowerOrder : List Row := [r0, r7, r1, r8, r4]
def lowerPool : List Nat := [0, 1, 2, 7, 8, 9, 11, 12, 16, 17, 18, 20, 21, 26, 28, 31, 35, 38, 47, 48, 53, 54, 56, 60, 63, 65, 71, 75, 82, 95, 105, 111, 123, 129, 130, 157, 161, 216, 217, 254, 255, 257, 266, 446, 564, 565, 590, 652, 860, 991, 994, 1018, 2201, 2643, 2999, 3038, 3042, 3142, 3302, 3834, 3881, 3882, 3914, 4099, 4530, 4531, 5728, 5731, 5732, 5733, 5734, 5737, 5738, 5739]
theorem lower_raf_checked : checkSupport rows food lower lowerOrder 0 = true := by decide +kernel
theorem lower_raf : RAF lower food := checked_raf _ _ _ _ _ lower_raf_checked
theorem lower_closed_checked : checkClosed rows lower food lowerPool = true := by decide +kernel
theorem lower_closed : ClosedRAF rows lower food := checked_closed _ _ _ _ lower_raf lower_closed_checked
theorem whole_closed : ClosedRAF rows rows food := ⟨whole_raf, fun _ hr _ _ => hr⟩
theorem lower_proper : Subrows lower rows ∧ ¬ Subrows rows lower := by
  unfold Subrows
  decide +kernel
end RAFBiochemicalLiteral.SmallSource
