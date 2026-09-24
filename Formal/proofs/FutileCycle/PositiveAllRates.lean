import proofs.FutileCycle.PositiveCore
import proofs.DUnstableCores.PositiveRealChild

namespace FutileCycle
open Matrix DUnstableCores

theorem positive_all_rates (n : ℕ) (hn : 2 ≤ n)
    (d : PositiveIndex n → ℝ) (hd : ∀ i, 0 < d i) :
    HasPositiveRealEigenpair (rightScale (positiveRealMatrix n hn) d) := by
  have hbase : (positiveRealMatrix n hn).det = 1 := by
    have hh := congrArg (Int.castRingHom ℝ) (positive_det n hn)
    simpa only [RingHom.map_det, map_one] using hh
  have hmat : rightScale (positiveRealMatrix n hn) d =
      positiveRealMatrix n hn * diagonal d := by ext i j; simp [rightScale]
  have hdet : 0 < (rightScale (positiveRealMatrix n hn) d).det := by
    rw [hmat, det_mul, hbase, one_mul, det_diagonal]
    exact Finset.prod_pos (fun i _ => hd i)
  have hneg : (-(rightScale (positiveRealMatrix n hn) d)).det < 0 := by
    rw [det_neg, positive_dimension n hn, pow_add, pow_mul]
    norm_num
    exact hdet
  obtain ⟨lam,hlam,hroot⟩ := monic_negative_constant_has_positive_root
    (rightScale (positiveRealMatrix n hn) d).charpoly
    (rightScale (positiveRealMatrix n hn) d).charpoly_monic
    (by rwa [← det_neg_eq_charpoly_coeff_zero])
  exact charpoly_positive_root_implies_positiveRealEigenpair hlam hroot

theorem positive_all_rates_minimal (n : ℕ) (hn : 2 ≤ n)
    (d : PositiveIndex n → ℝ) (hd : ∀ i, 0 < d i) :
    MinimalUnstable (rightScale (positiveRealMatrix n hn) d) := by
  refine ⟨hasPositiveRealEigenpair_implies_hurwitzUnstable (positive_all_rates n hn d hd),?_⟩
  intro s hs
  exact positive_proper_scaling n hn s hs (fun i => d i.val) (fun i => hd i.val)

end FutileCycle
