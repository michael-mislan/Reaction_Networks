import proofs.RAF1519.Reservoir.ReconstructionBounds
import proofs.RAF1519.Reservoir.Secant

namespace RAF1519.Reservoir
noncomputable section
open Set

def lowBoxLower (i : Fin 6) : ℝ := match i.val with
  | 0 => (1276378483/100000000:ℝ)
  | 1 => (1011737993/50000000:ℝ)
  | 2 => (9651939/10000000:ℝ)
  | 3 => (54079487/6250000:ℝ)
  | 4 => (5601711/10000000:ℝ)
  | 5 => (254213/6250000:ℝ)
  | _ => 0

def lowBoxUpper (i : Fin 6) : ℝ := match i.val with
  | 0 => (638191873/50000000:ℝ)
  | 1 => (404695287/20000000:ℝ)
  | 2 => (48259729/50000000:ℝ)
  | 3 => (173054489/20000000:ℝ)
  | 4 => (14004287/25000000:ℝ)
  | 5 => (4067413/100000000:ℝ)
  | _ => 0

theorem low_box_positive (i : Fin 6) : 0 < lowBoxLower i := by
  fin_cases i <;> norm_num [lowBoxLower]

private theorem low_enclosure (i : Fin 6) :
    lowBoxLower i < reconstructionLower (4067409/100000000:ℝ) (1016853/25000000:ℝ) i ∧
      reconstructionUpper (4067409/100000000:ℝ) (1016853/25000000:ℝ) i < lowBoxUpper i := by
  fin_cases i <;> norm_num [lowBoxLower,lowBoxUpper,reconstructionLower,
    reconstructionUpper,substrate,resource,catalyst,reservoir,uptake]

theorem low_root_box (s : ℝ) (hs : s ∈ Icc (4067409/100000000:ℝ) (1016853/25000000:ℝ)) :
    ∀ i, lowBoxLower i < state s i ∧ state s i < lowBoxUpper i := by
  have hb := reconstruction_bounds (4067409/100000000:ℝ) (1016853/25000000:ℝ) s (by norm_num) (by norm_num) hs
  intro i
  exact ⟨(low_enclosure i).1.trans_le (hb i).1,
    (hb i).2.trans_lt (low_enclosure i).2⟩

def highBoxLower (i : Fin 6) : ℝ := match i.val with
  | 0 => (515578777/25000000:ℝ)
  | 1 => (618621621/50000000:ℝ)
  | 2 => (284948539/100000000:ℝ)
  | 3 => (1545695227/50000000:ℝ)
  | 4 => (5002203/25000000:ℝ)
  | 5 => (7014929/100000000:ℝ)
  | _ => 0

def highBoxUpper (i : Fin 6) : ℝ := match i.val with
  | 0 => (2062371061/100000000:ℝ)
  | 1 => (1237244679/100000000:ℝ)
  | 2 => (17809319/6250000:ℝ)
  | 3 => (3091398157/100000000:ℝ)
  | 4 => (20008853/100000000:ℝ)
  | 5 => (3507467/50000000:ℝ)
  | _ => 0

theorem high_box_positive (i : Fin 6) : 0 < highBoxLower i := by
  fin_cases i <;> norm_num [highBoxLower]

private theorem high_enclosure (i : Fin 6) :
    highBoxLower i < reconstructionLower (701493/10000000:ℝ) (7014933/100000000:ℝ) i ∧
      reconstructionUpper (701493/10000000:ℝ) (7014933/100000000:ℝ) i < highBoxUpper i := by
  fin_cases i <;> norm_num [highBoxLower,highBoxUpper,reconstructionLower,
    reconstructionUpper,substrate,resource,catalyst,reservoir,uptake]

theorem high_root_box (s : ℝ) (hs : s ∈ Icc (701493/10000000:ℝ) (7014933/100000000:ℝ)) :
    ∀ i, highBoxLower i < state s i ∧ state s i < highBoxUpper i := by
  have hb := reconstruction_bounds (701493/10000000:ℝ) (7014933/100000000:ℝ) s (by norm_num) (by norm_num) hs
  intro i
  exact ⟨(high_enclosure i).1.trans_le (hb i).1,
    (hb i).2.trans_lt (high_enclosure i).2⟩

end
end RAF1519.Reservoir
