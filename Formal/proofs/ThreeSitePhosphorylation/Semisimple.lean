import proofs.ThreeSitePhosphorylation.SpectrumNecessary
import proofs.ThreeSitePhosphorylation.SimpleRoot

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 300000

def companionLeft (r : ℝ) (z : ℂ) : Fin 9 → ℂ :=
  ![(((1/1:ℝ)+r*(0/1:ℝ)):ℂ)*z^8 + (((21549480866197/53063010000:ℝ)+r*(716/6045:ℝ)):ℂ)*z^7 + (((1914250662484005497/49272795000000:ℝ)+r*(244167141079021/5173643475000:ℝ)):ℂ)*z^6 + (((3070471513831161895424219/2522151194062500000:ℝ)+r*(1743145840777470340069/403544191050000000:ℝ)):ℂ)*z^5 + (((178228249672628679513269034107/15132907164375000000000:ℝ)+r*(41210428898350734288350941/302658143287500000000:ℝ)):ℂ)*z^4 + (((3747333761964530151289376279869/151329071643750000000000:ℝ)+r*(19351917652493567002237891771/15132907164375000000000:ℝ)):ℂ)*z^3 + (((1095227502621761760478226249101/226993607465625000000000:ℝ)+r*(298391200108946577505242797723/113496803732812500000000:ℝ)):ℂ)*z^2 + (((676438287388827146536247537/1269894307500000000000:ℝ)+r*(15669391757369638993598066707/13968837382500000000000:ℝ)):ℂ)*z^1 + (((2365405597729059858828139/17908765875000000000:ℝ)+r*(2369048939115567901134889/17908765875000000000:ℝ)):ℂ)*z^0,
    (((1/1:ℝ)+r*(0/1:ℝ)):ℂ)*z^7 + (((21549480866197/53063010000:ℝ)+r*(716/6045:ℝ)):ℂ)*z^6 + (((1914250662484005497/49272795000000:ℝ)+r*(244167141079021/5173643475000:ℝ)):ℂ)*z^5 + (((3070471513831161895424219/2522151194062500000:ℝ)+r*(1743145840777470340069/403544191050000000:ℝ)):ℂ)*z^4 + (((178228249672628679513269034107/15132907164375000000000:ℝ)+r*(41210428898350734288350941/302658143287500000000:ℝ)):ℂ)*z^3 + (((3747333761964530151289376279869/151329071643750000000000:ℝ)+r*(19351917652493567002237891771/15132907164375000000000:ℝ)):ℂ)*z^2 + (((1095227502621761760478226249101/226993607465625000000000:ℝ)+r*(298391200108946577505242797723/113496803732812500000000:ℝ)):ℂ)*z^1 + (((676438287388827146536247537/1269894307500000000000:ℝ)+r*(15669391757369638993598066707/13968837382500000000000:ℝ)):ℂ)*z^0,
    (((1/1:ℝ)+r*(0/1:ℝ)):ℂ)*z^6 + (((21549480866197/53063010000:ℝ)+r*(716/6045:ℝ)):ℂ)*z^5 + (((1914250662484005497/49272795000000:ℝ)+r*(244167141079021/5173643475000:ℝ)):ℂ)*z^4 + (((3070471513831161895424219/2522151194062500000:ℝ)+r*(1743145840777470340069/403544191050000000:ℝ)):ℂ)*z^3 + (((178228249672628679513269034107/15132907164375000000000:ℝ)+r*(41210428898350734288350941/302658143287500000000:ℝ)):ℂ)*z^2 + (((3747333761964530151289376279869/151329071643750000000000:ℝ)+r*(19351917652493567002237891771/15132907164375000000000:ℝ)):ℂ)*z^1 + (((1095227502621761760478226249101/226993607465625000000000:ℝ)+r*(298391200108946577505242797723/113496803732812500000000:ℝ)):ℂ)*z^0,
    (((1/1:ℝ)+r*(0/1:ℝ)):ℂ)*z^5 + (((21549480866197/53063010000:ℝ)+r*(716/6045:ℝ)):ℂ)*z^4 + (((1914250662484005497/49272795000000:ℝ)+r*(244167141079021/5173643475000:ℝ)):ℂ)*z^3 + (((3070471513831161895424219/2522151194062500000:ℝ)+r*(1743145840777470340069/403544191050000000:ℝ)):ℂ)*z^2 + (((178228249672628679513269034107/15132907164375000000000:ℝ)+r*(41210428898350734288350941/302658143287500000000:ℝ)):ℂ)*z^1 + (((3747333761964530151289376279869/151329071643750000000000:ℝ)+r*(19351917652493567002237891771/15132907164375000000000:ℝ)):ℂ)*z^0,
    (((1/1:ℝ)+r*(0/1:ℝ)):ℂ)*z^4 + (((21549480866197/53063010000:ℝ)+r*(716/6045:ℝ)):ℂ)*z^3 + (((1914250662484005497/49272795000000:ℝ)+r*(244167141079021/5173643475000:ℝ)):ℂ)*z^2 + (((3070471513831161895424219/2522151194062500000:ℝ)+r*(1743145840777470340069/403544191050000000:ℝ)):ℂ)*z^1 + (((178228249672628679513269034107/15132907164375000000000:ℝ)+r*(41210428898350734288350941/302658143287500000000:ℝ)):ℂ)*z^0,
    (((1/1:ℝ)+r*(0/1:ℝ)):ℂ)*z^3 + (((21549480866197/53063010000:ℝ)+r*(716/6045:ℝ)):ℂ)*z^2 + (((1914250662484005497/49272795000000:ℝ)+r*(244167141079021/5173643475000:ℝ)):ℂ)*z^1 + (((3070471513831161895424219/2522151194062500000:ℝ)+r*(1743145840777470340069/403544191050000000:ℝ)):ℂ)*z^0,
    (((1/1:ℝ)+r*(0/1:ℝ)):ℂ)*z^2 + (((21549480866197/53063010000:ℝ)+r*(716/6045:ℝ)):ℂ)*z^1 + (((1914250662484005497/49272795000000:ℝ)+r*(244167141079021/5173643475000:ℝ)):ℂ)*z^0,
    (((1/1:ℝ)+r*(0/1:ℝ)):ℂ)*z^1 + (((21549480866197/53063010000:ℝ)+r*(716/6045:ℝ)):ℂ)*z^0,
    (((1/1:ℝ)+r*(0/1:ℝ)):ℂ)*z^0]

theorem companion_left_residual (r : ℝ) (z : ℂ) :
    Matrix.vecMul (companionLeft r z) (companionSource r) =
      z • companionLeft r z - Pi.single 0 (candidatePolynomial r z) := by
  ext i
  fin_cases i <;>
    simp [companionLeft,companionSource,candidatePolynomial,Matrix.vecMul,
      dotProduct,Fin.sum_univ_succ] <;> ring

theorem companion_left_pairing (r : ℝ) (z : ℂ) :
    dotProduct (companionLeft r z) (powerVector z) = candidateSlope r z := by
  simp [companionLeft,powerVector,candidateSlope,dotProduct,Fin.sum_univ_succ]
  ring

theorem companion_eigenvector_form (r : ℝ) (z : ℂ) (y : Fin 9 → ℂ)
    (he : (companionSource r).mulVec y = z • y) : y = y 0 • powerVector z := by
  have h1 : y 1 = z^1*y 0 := by
    have hh := congrFun he (⟨0,by decide⟩ : Fin 9)
    have hk : y 1 = z*y 0 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    simpa using hk
  have h2 : y 2 = z^2*y 0 := by
    have hh := congrFun he (⟨1,by decide⟩ : Fin 9)
    have hk : y 2 = z*y 1 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    rw [hk,h1]
    ring
  have h3 : y 3 = z^3*y 0 := by
    have hh := congrFun he (⟨2,by decide⟩ : Fin 9)
    have hk : y 3 = z*y 2 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    rw [hk,h2]
    ring
  have h4 : y 4 = z^4*y 0 := by
    have hh := congrFun he (⟨3,by decide⟩ : Fin 9)
    have hk : y 4 = z*y 3 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    rw [hk,h3]
    ring
  have h5 : y 5 = z^5*y 0 := by
    have hh := congrFun he (⟨4,by decide⟩ : Fin 9)
    have hk : y 5 = z*y 4 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    rw [hk,h4]
    ring
  have h6 : y 6 = z^6*y 0 := by
    have hh := congrFun he (⟨5,by decide⟩ : Fin 9)
    have hk : y 6 = z*y 5 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    rw [hk,h5]
    ring
  have h7 : y 7 = z^7*y 0 := by
    have hh := congrFun he (⟨6,by decide⟩ : Fin 9)
    have hk : y 7 = z*y 6 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    rw [hk,h6]
    ring
  have h8 : y 8 = z^8*y 0 := by
    have hh := congrFun he (⟨7,by decide⟩ : Fin 9)
    have hk : y 8 = z*y 7 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    rw [hk,h7]
    ring
  ext i
  fin_cases i <;> simp [powerVector,h1,h2,h3,h4,h5,h6,h7,h8,mul_comm]

theorem companion_no_jordan_chain (r : ℝ) (z : ℂ)
    (hs : candidateSlope r z ≠ 0) (v u : Fin 9 → ℂ) (hv : v ≠ 0)
    (he : (companionSource r).mulVec v = z • v) :
    (companionSource r).mulVec u-z • u ≠ v := by
  have hp := companion_eigenvalue_root r z v hv he
  have hf := companion_eigenvector_form r z v he
  have hv0 : v 0 ≠ 0 := by
    intro h
    rw [h,zero_smul] at hf
    exact hv hf
  intro hu
  have hh := congrArg (fun y => dotProduct (companionLeft r z) y) hu
  dsimp only at hh
  rw [dotProduct_sub,Matrix.dotProduct_mulVec,companion_left_residual,hp,
    Pi.single_zero,sub_zero,smul_dotProduct,dotProduct_smul] at hh
  have hpair : dotProduct (companionLeft r z) v = v 0*candidateSlope r z := by
    conv_lhs => rw [hf]
    rw [dotProduct_smul,companion_left_pairing]
    rfl
  rw [hpair] at hh
  have hz : v 0*candidateSlope r z=0 := by simpa using hh.symm
  exact (mul_ne_zero hv0 hs) hz

end
end ThreeSitePhosphorylation
