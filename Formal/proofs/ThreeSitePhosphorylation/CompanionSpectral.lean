import proofs.ThreeSitePhosphorylation.Companion
import proofs.ThreeSitePhosphorylation.Spectral
import proofs.ThreeSitePhosphorylation.PolynomialBasis

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 4000000

def companionBasis : Matrix (Fin 9) (Fin 9) ℂ := companionBasisQ.map (algebraMap ℚ ℂ)
def companionInverse : Matrix (Fin 9) (Fin 9) ℂ := companionInverseQ.map (algebraMap ℚ ℂ)
def complexSource (r : ℝ) : Matrix (Fin 9) (Fin 9) ℂ := (sourceMatrix r).map (algebraMap ℝ ℂ)
def companionSource (r : ℝ) : Matrix (Fin 9) (Fin 9) ℂ :=
  !![0,1,0,0,0,0,0,0,0;
    0,0,1,0,0,0,0,0,0;
    0,0,0,1,0,0,0,0,0;
    0,0,0,0,1,0,0,0,0;
    0,0,0,0,0,1,0,0,0;
    0,0,0,0,0,0,1,0,0;
    0,0,0,0,0,0,0,1,0;
    0,0,0,0,0,0,0,0,1;
    -(((1182316803067886887/3061327500000000):ℂ)+(r:ℂ)*(1182316803067886887/3061327500000000)),-(((2365405597729059858828139/17908765875000000000):ℂ)+(r:ℂ)*(2369048939115567901134889/17908765875000000000)),-(((676438287388827146536247537/1269894307500000000000):ℂ)+(r:ℂ)*(15669391757369638993598066707/13968837382500000000000)),-(((1095227502621761760478226249101/226993607465625000000000):ℂ)+(r:ℂ)*(298391200108946577505242797723/113496803732812500000000)),-(((3747333761964530151289376279869/151329071643750000000000):ℂ)+(r:ℂ)*(19351917652493567002237891771/15132907164375000000000)),-(((178228249672628679513269034107/15132907164375000000000):ℂ)+(r:ℂ)*(41210428898350734288350941/302658143287500000000)),-(((3070471513831161895424219/2522151194062500000):ℂ)+(r:ℂ)*(1743145840777470340069/403544191050000000)),-(((1914250662484005497/49272795000000):ℂ)+(r:ℂ)*(244167141079021/5173643475000)),-(((21549480866197/53063010000):ℂ)+(r:ℂ)*(716/6045))]

theorem companion_inverse_complex : companionInverse*companionBasis = 1 := by
  unfold companionInverse companionBasis
  rw [← Matrix.map_mul,companion_inverse]
  simp

theorem companion_inverse_complex_right : companionBasis*companionInverse = 1 :=
  mul_eq_one_comm.mp companion_inverse_complex

theorem basis_powerVector (z : ℂ) : companionBasis.mulVec (powerVector z) = adjugateVector z := by
  ext i
  fin_cases i <;>
    norm_num [companionBasis,companionBasisQ,powerVector,adjugateVector,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem companion_powerVector (r : ℝ) (z : ℂ) :
    (companionSource r).mulVec (powerVector z) =
      z • powerVector z - Pi.single 8 (candidatePolynomial r z) := by
  ext i
  fin_cases i <;>
    simp [companionSource,powerVector,candidatePolynomial,Matrix.mulVec,
      dotProduct,Fin.sum_univ_succ] <;> ring

theorem basis_single (z : ℂ) : companionBasis.mulVec (Pi.single 8 z) = Pi.single 6 z := by
  change companionBasis.mulVec (Pi.single (⟨8,by decide⟩ : Fin 9) z) =
    Pi.single (⟨6,by decide⟩ : Fin 9) z
  ext i
  fin_cases i <;>
    norm_num [companionBasis,companionBasisQ,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Pi.single_apply,Fin.ext_iff]

theorem source_companion_identity (r : ℝ) :
    complexSource r*companionBasis = companionBasis*companionSource r := by
  apply matrix_eq_of_powerVector
  intro z
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,basis_powerVector,
    companion_powerVector,Matrix.mulVec_sub,Matrix.mulVec_smul,basis_powerVector,basis_single]
  ext i
  simpa [complexSource,Pi.single_apply,eq_comm] using adjugate_residual r z i

end
end ThreeSitePhosphorylation

