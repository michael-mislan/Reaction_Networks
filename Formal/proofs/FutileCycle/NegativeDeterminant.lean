import proofs.FutileCycle.NegativeWitness

namespace FutileCycle

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem negativeMatrix_det : negativeMatrix.det = 1 := by
  norm_num [negativeMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.det_fin_zero, Matrix.submatrix, Fin.succAbove]
  decide

end FutileCycle
