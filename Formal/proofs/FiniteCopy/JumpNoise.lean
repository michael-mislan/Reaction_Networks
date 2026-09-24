import proofs.FiniteCopy.LocalNonlinear

namespace FiniteCopy

theorem linear_four_sq (a b c d : ℝ) (x : Point) :
    (a*x 0+b*x 1+c*x 2+d*x 3)^2 ≤ (a^2+b^2+c^2+d^2)*normSq x := by
  have hid : (a^2+b^2+c^2+d^2)*normSq x-(a*x 0+b*x 1+c*x 2+d*x 3)^2 =
      (a*x 1-b*x 0)^2+(a*x 2-c*x 0)^2+(a*x 3-d*x 0)^2+
      (b*x 2-c*x 1)^2+(b*x 3-d*x 1)^2+(c*x 3-d*x 2)^2 := by
    unfold normSq
    ring
  have hn : 0 ≤ (a^2+b^2+c^2+d^2)*normSq x-(a*x 0+b*x 1+c*x 2+d*x 3)^2 := by
    rw [hid]
    positivity
  linarith only [hn]

theorem lowjump_energy_bound (r : Fin 13) :
    0 ≤ lowEnergy (jump r) ∧ lowEnergy (jump r) ≤ 210 := by
  fin_cases r <;> norm_num [lowEnergy,jump,Matrix.cons_val_two,Matrix.cons_val_three]

theorem lowjump_pair_sq (x : Point) (r : Fin 13) :
    (2*lowPair x (jump r))^2 ≤ 100000*normSq x := by
  fin_cases r
  · have h := linear_four_sq (308269/250000 : ℝ) (-307053/250000 : ℝ) (2082397/500000 : ℝ) (3299537/500000 : ℝ) x
    norm_num only at h
    norm_num [lowPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (-308269/250000 : ℝ) (307053/250000 : ℝ) (-2082397/500000 : ℝ) (-3299537/500000 : ℝ) x
    norm_num only at h
    norm_num [lowPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (549419/250000 : ℝ) (-1095071/500000 : ℝ) (3411049/500000 : ℝ) (5338627/500000 : ℝ) x
    norm_num only at h
    norm_num [lowPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (-549419/250000 : ℝ) (1095071/500000 : ℝ) (-3411049/500000 : ℝ) (-5338627/500000 : ℝ) x
    norm_num only at h
    norm_num [lowPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (1247209/500000 : ℝ) (-622121/250000 : ℝ) (839177/125000 : ℝ) (4840179/500000 : ℝ) x
    norm_num only at h
    norm_num [lowPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (-1247209/500000 : ℝ) (622121/250000 : ℝ) (-839177/125000 : ℝ) (-4840179/500000 : ℝ) x
    norm_num only at h
    norm_num [lowPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (1115801/500000 : ℝ) (-153427/125000 : ℝ) (2346047/500000 : ℝ) (688977/100000 : ℝ) x
    norm_num only at h
    norm_num [lowPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (-1115801/500000 : ℝ) (153427/125000 : ℝ) (-2346047/500000 : ℝ) (-688977/100000 : ℝ) x
    norm_num only at h
    norm_num [lowPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (-153427/125000 : ℝ) (1111499/500000 : ℝ) (-2339313/500000 : ℝ) (-214649/31250 : ℝ) x
    norm_num only at h
    norm_num [lowPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (153427/125000 : ℝ) (-1111499/500000 : ℝ) (2339313/500000 : ℝ) (214649/31250 : ℝ) x
    norm_num only at h
    norm_num [lowPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (284531/50000 : ℝ) (-467783/100000 : ℝ) (7031407/500000 : ℝ) (5162077/250000 : ℝ) x
    norm_num only at h
    norm_num [lowPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (-284531/50000 : ℝ) (467783/100000 : ℝ) (-7031407/500000 : ℝ) (-5162077/250000 : ℝ) x
    norm_num only at h
    norm_num [lowPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (-688977/100000 : ℝ) (214649/31250 : ℝ) (-5089403/250000 : ℝ) (-15517433/500000 : ℝ) x
    norm_num only at h
    norm_num [lowPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]

theorem highjump_energy_bound (r : Fin 13) :
    0 ≤ highEnergy (jump r) ∧ highEnergy (jump r) ≤ 210 := by
  fin_cases r <;> norm_num [highEnergy,jump,Matrix.cons_val_two,Matrix.cons_val_three]

theorem highjump_pair_sq (x : Point) (r : Fin 13) :
    (2*highPair x (jump r))^2 ≤ 100000*normSq x := by
  fin_cases r
  · have h := linear_four_sq (347279/500000 : ℝ) (-257633/100000 : ℝ) (2264267/500000 : ℝ) (347919/50000 : ℝ) x
    norm_num only at h
    norm_num [highPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (-347279/500000 : ℝ) (257633/100000 : ℝ) (-2264267/500000 : ℝ) (-347919/50000 : ℝ) x
    norm_num only at h
    norm_num [highPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (231441/100000 : ℝ) (-690277/100000 : ℝ) (5823513/500000 : ℝ) (1771967/100000 : ℝ) x
    norm_num only at h
    norm_num [highPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (-231441/100000 : ℝ) (690277/100000 : ℝ) (-5823513/500000 : ℝ) (-1771967/100000 : ℝ) x
    norm_num only at h
    norm_num [highPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (37364/15625 : ℝ) (-1665129/250000 : ℝ) (22301/2000 : ℝ) (8362441/500000 : ℝ) x
    norm_num only at h
    norm_num [highPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (-37364/15625 : ℝ) (1665129/250000 : ℝ) (-22301/2000 : ℝ) (-8362441/500000 : ℝ) x
    norm_num only at h
    norm_num [highPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (211521/125000 : ℝ) (-115949/50000 : ℝ) (2352853/500000 : ℝ) (1755029/250000 : ℝ) x
    norm_num only at h
    norm_num [highPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (-211521/125000 : ℝ) (115949/50000 : ℝ) (-2352853/500000 : ℝ) (-1755029/250000 : ℝ) x
    norm_num only at h
    norm_num [highPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (-115949/50000 : ℝ) (1083497/125000 : ℝ) (-6781643/500000 : ℝ) (-2558257/125000 : ℝ) x
    norm_num only at h
    norm_num [highPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (115949/50000 : ℝ) (-1083497/125000 : ℝ) (6781643/500000 : ℝ) (2558257/125000 : ℝ) x
    norm_num only at h
    norm_num [highPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (1425829/250000 : ℝ) (-831621/62500 : ℝ) (11487349/500000 : ℝ) (2156643/62500 : ℝ) x
    norm_num only at h
    norm_num [highPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (-1425829/250000 : ℝ) (831621/62500 : ℝ) (-11487349/500000 : ℝ) (-2156643/62500 : ℝ) x
    norm_num only at h
    norm_num [highPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]
  · have h := linear_four_sq (-1755029/250000 : ℝ) (2558257/125000 : ℝ) (-4305569/125000 : ℝ) (-26082111/500000 : ℝ) x
    norm_num only at h
    norm_num [highPair,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg x]

end FiniteCopy
