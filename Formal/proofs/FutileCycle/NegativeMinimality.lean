import proofs.FutileCycle.MaskCoverage
import proofs.FutileCycle.AnnihilatorSoundness
import proofs.FutileCycle.PrincipalExtension
import proofs.FutileCycle.ExceptionalRestriction

namespace FutileCycle
noncomputable section
open Matrix DUnstableCores

@[simp] theorem bit31_0 : Nat.testBit 31 0 = true := by decide
@[simp] theorem bit31_1 : Nat.testBit 31 1 = true := by decide
@[simp] theorem bit31_2 : Nat.testBit 31 2 = true := by decide
@[simp] theorem bit31_3 : Nat.testBit 31 3 = true := by decide
@[simp] theorem bit31_4 : Nat.testBit 31 4 = true := by decide
@[simp] theorem bit31_5 : Nat.testBit 31 5 = false := by decide

def negativeMaskedComplex (m : Fin 64) : Matrix (Fin 6) (Fin 6) ℂ :=
  (negativeMasked m).map (Int.castRingHom ℂ)

theorem exceptional_mask_no_rhp (z : ℂ) (v : Fin 6 → ℂ) (hv : v ≠ 0)
    (he : negativeMaskedComplex 31 *ᵥ v = z • v) : ¬0 < z.re := by
  intro hz
  have hz0 : z ≠ 0 := by intro hh; simp [hh] at hz
  have h5 := congrFun he 5
  norm_num [negativeMaskedComplex, negativeMasked, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at h5
  have hv5 : v 5 = 0 := h5.resolve_left hz0
  let w : Fin 5 → ℂ := fun i => v i.castSucc
  have hw : w ≠ 0 := by
    intro hh
    apply hv
    funext i
    fin_cases i
    all_goals first
      | exact congrFun hh 0
      | exact congrFun hh 1
      | exact congrFun hh 2
      | exact congrFun hh 3
      | exact congrFun hh 4
      | exact hv5
  have hew : exceptionalMatrix *ᵥ w = z • w := by
    ext i
    have hh := congrFun he i.castSucc
    fin_cases i <;>
      simpa [w, exceptionalMatrix, negativeMaskedComplex, negativeMasked,
        negativeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hh
  exact exceptional_no_rhp z w hw hew hz

theorem negative_mask_no_rhp (m : Fin 64) (hm : m ≠ 63)
    (z : ℂ) (v : Fin 6 → ℂ) (hv : v ≠ 0)
    (he : negativeMaskedComplex m *ᵥ v = z • v) : ¬0 < z.re := by
  by_cases h31 : m = 31
  · subst m
    exact exceptional_mask_no_rhp z v hv he
  · let F : Matrix (Fin 6) (Fin 6) ℤ →+* Matrix (Fin 6) (Fin 6) ℂ :=
      (Int.castRingHom ℂ).mapMatrix
    have hh := congrArg F (negativeMasked_annihilator m h31 hm)
    have hA : (negativeMaskedComplex m)^2 * (negativeMaskedComplex m+1)^4 *
        (negativeMaskedComplex m+2)^2 = 0 := by
      simpa only [map_mul, map_pow, map_add, map_one, map_ofNat, map_zero] using hh
    exact annihilator_no_rhp _ hA z v hv he

theorem negative_principal_no_rhp (p : Fin 6 → Prop) [DecidablePred p]
    (hp : ∃ i, ¬p i) (z : ℂ) (v : {i // p i} → ℂ) (hv : v ≠ 0)
    (he : (complexify negativeRealMatrix).submatrix Subtype.val Subtype.val *ᵥ v = z • v) :
    ¬0 < z.re := by
  obtain ⟨m,hm⟩ := mask_coverage (fun i => decide (p i))
  have hm63 : m ≠ 63 := by
    intro hh
    obtain ⟨i,hi⟩ := hp
    have hc := hm i
    rw [hh] at hc
    simp [full_mask, hi] at hc
  obtain ⟨w,hw,hew⟩ := principal_eigenpair_extends (complexify negativeRealMatrix) p z v hv he
  have hmat : padded (complexify negativeRealMatrix) p = negativeMaskedComplex m := by
    ext i j
    simp [padded, negativeMaskedComplex, negativeMasked, hm, complexify,
      negativeRealMatrix, Matrix.map_apply]
  rw [hmat] at hew
  exact negative_mask_no_rhp m hm63 z w hw hew

end
end FutileCycle
