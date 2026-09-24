import proofs.FutileCycle.Lyapunov
import proofs.FutileCycle.NegativeSpectrum

namespace FutileCycle
noncomputable section
open Matrix DUnstableCores
open scoped ComplexOrder

def exceptionalMatrix : Matrix (Fin 5) (Fin 5) ℂ :=
  !![-1,0,0,-1,0; 0,-1,0,0,1; -1,0,-1,0,1;
    0,-1,0,-1,0; 0,0,1,0,-1]

def lyapunovQ : Matrix (Fin 5) (Fin 5) ℂ :=
  !![1443,770,-1334,-1169,-1041;
    770,1133,-371,-1024,153;
    -1334,-371,1627,895,1518;
    -1169,-1024,895,1278,456;
    -1041,153,1518,456,1780]

def lyapunovR : Matrix (Fin 5) (Fin 5) ℂ :=
  !![1,770/1443,-1334/1443,-1169/1443,-347/481;
    0,1,491827/1042019,-577502/1042019,1022349/1042019;
    0,0,1,30585/2226418,2114931/2226418;
    0,0,0,1,5181/247667;
    0,0,0,0,1]

def lyapunovDiagonal : Fin 5 → ℂ :=
  ![1443,1042019/1443,242679562/1042019,242961327/2226418,30634559/247667]

theorem lyapunovQ_gram :
    lyapunovQ = lyapunovR.conjTranspose * diagonal lyapunovDiagonal * lyapunovR := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lyapunovQ, lyapunovR, lyapunovDiagonal, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.diagonal, map_ofNat]

theorem lyapunovQ_nonnegative : lyapunovQ.PosSemidef := by
  rw [lyapunovQ_gram]
  apply Matrix.PosSemidef.conjTranspose_mul_mul_same
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [lyapunovDiagonal] <;> positivity

theorem exceptional_lyapunov_identity :
    exceptionalMatrix.conjTranspose * lyapunovQ + lyapunovQ * exceptionalMatrix =
      -(218 : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [exceptionalMatrix, lyapunovQ, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply]

theorem exceptional_no_rhp (z : ℂ) (v : Fin 5 → ℂ) (hv : v ≠ 0)
    (he : exceptionalMatrix *ᵥ v = z • v) : ¬0 < z.re := by
  exact lyapunov_no_rhp exceptionalMatrix lyapunovQ lyapunovQ_nonnegative 218
    (by norm_num) (by simpa using exceptional_lyapunov_identity) z v hv he

end
end FutileCycle
