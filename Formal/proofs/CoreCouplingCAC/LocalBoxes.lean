import proofs.CoreCouplingCAC.LocalBounds
import proofs.CoreCouplingCAC.Dynamics
import proofs.CoreCouplingCAC.ComparisonCertificates

namespace CoreCouplingCAC

noncomputable def lowLower : State := ⟨(12970413/1000000 : ℝ),(10014031/500000 : ℝ),(124473/125000 : ℝ),(8957499/1000000 : ℝ)⟩
noncomputable def lowUpper : State := ⟨(12970471/1000000 : ℝ),(2002809/100000 : ℝ),(199161/200000 : ℝ),(895753/100000 : ℝ)⟩
noncomputable def lowRootLower : State := ⟨(12970423/1000000 : ℝ),(2503509/125000 : ℝ),(497897/500000 : ℝ),(8957509/1000000 : ℝ)⟩
noncomputable def lowRootUpper : State := ⟨(12970461/1000000 : ℝ),(250351/12500 : ℝ),(199159/200000 : ℝ),(111969/12500 : ℝ)⟩
theorem low_root_enclosure (z : ℝ) (hz : z ∈ Set.Icc (497897/500000 : ℝ) (199159/200000 : ℝ)) :
    InBox (lift witnessRates z) lowRootLower lowRootUpper := by
  have h := lift_interval_enclosure (497897/500000 : ℝ) (199159/200000 : ℝ) z (by norm_num) hz.1 hz.2
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [lowerState,upperState] at h1 h2 h3 h4 h5 h6 h7 h8
  norm_num [InBox,lowRootLower,lowRootUpper]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
theorem low_jacobian_domination (x : State) (hx : InBox x lowLower lowUpper) :
    (∀ i, jacobian witnessRates (transform x) i i ≤ lowComparison i i) ∧
    (∀ i j, i ≠ j → |jacobian witnessRates (transform x) i j| ≤ lowComparison i j) := by
  rcases hx with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [lowLower,lowUpper] at h1 h2 h3 h4 h5 h6 h7 h8
  constructor
  · intro i; fin_cases i <;> simp only [jacobian,transform,witnessRates,lowComparison,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] <;> norm_num <;> linarith
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try { exact False.elim (hij rfl) }
    all_goals simp only [jacobian,transform,witnessRates,lowComparison,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    all_goals simp only [abs_le]
    all_goals try constructor
    all_goals norm_num
    all_goals linarith
theorem low_CAC_box (x : State) (hx : InBox x lowLower lowUpper) :
    (1/10000:ℝ) ≤ (coreZH witnessRates x).1 ∧ (1/10000:ℝ) ≤ (coreZH witnessRates x).2 := by
  rcases hx with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [lowLower,lowUpper] at h1 h2 h3 h4 h5 h6 h7 h8
  have hslo : (124473/125000 : ℝ)^2 ≤ x.z^2 := by nlinarith [sq_nonneg (x.z-(124473/125000 : ℝ))]
  have hshi : x.z^2 ≤ (199161/200000 : ℝ)^2 := by nlinarith [sq_nonneg ((199161/200000 : ℝ)-x.z)]
  norm_num [coreZH,witnessRates]
  constructor <;> nlinarith
theorem low_energy_row_bound (i : Fin 4) :
    lowLeft i*(∑ j : Fin 4, lowComparison i j*lowRight j)+
      lowRight i*(∑ j : Fin 4, lowComparison j i*lowLeft j) ≤
        -(1/100:ℝ)*(lowLeft i*lowRight i) := by
  fin_cases i <;> norm_num [lowLeft,lowRight,lowComparison,Fin.sum_univ_succ]

noncomputable def highLower : State := ⟨(10469361/500000 : ℝ),(753561/62500 : ℝ),(2976357/1000000 : ℝ),(32668053/1000000 : ℝ)⟩
noncomputable def highUpper : State := ⟨(2617347/125000 : ℝ),(12056999/1000000 : ℝ),(1488189/500000 : ℝ),(4083511/125000 : ℝ)⟩
noncomputable def highRootLower : State := ⟨(5234683/250000 : ℝ),(6028493/500000 : ℝ),(2976367/1000000 : ℝ),(32668063/1000000 : ℝ)⟩
noncomputable def highRootUpper : State := ⟨(10469383/500000 : ℝ),(12056989/1000000 : ℝ),(186023/62500 : ℝ),(16334039/500000 : ℝ)⟩
theorem high_root_enclosure (z : ℝ) (hz : z ∈ Set.Icc (2976367/1000000 : ℝ) (186023/62500 : ℝ)) :
    InBox (lift witnessRates z) highRootLower highRootUpper := by
  have h := lift_interval_enclosure (2976367/1000000 : ℝ) (186023/62500 : ℝ) z (by norm_num) hz.1 hz.2
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [lowerState,upperState] at h1 h2 h3 h4 h5 h6 h7 h8
  norm_num [InBox,highRootLower,highRootUpper]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
theorem high_jacobian_domination (x : State) (hx : InBox x highLower highUpper) :
    (∀ i, jacobian witnessRates (transform x) i i ≤ highComparison i i) ∧
    (∀ i j, i ≠ j → |jacobian witnessRates (transform x) i j| ≤ highComparison i j) := by
  rcases hx with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [highLower,highUpper] at h1 h2 h3 h4 h5 h6 h7 h8
  constructor
  · intro i; fin_cases i <;> simp only [jacobian,transform,witnessRates,highComparison,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] <;> norm_num <;> linarith
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try { exact False.elim (hij rfl) }
    all_goals simp only [jacobian,transform,witnessRates,highComparison,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    all_goals simp only [abs_le]
    all_goals try constructor
    all_goals norm_num
    all_goals linarith
theorem high_CAC_box (x : State) (hx : InBox x highLower highUpper) :
    (1/10000:ℝ) ≤ (coreZH witnessRates x).1 ∧ (1/10000:ℝ) ≤ (coreZH witnessRates x).2 := by
  rcases hx with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [highLower,highUpper] at h1 h2 h3 h4 h5 h6 h7 h8
  have hslo : (2976357/1000000 : ℝ)^2 ≤ x.z^2 := by nlinarith [sq_nonneg (x.z-(2976357/1000000 : ℝ))]
  have hshi : x.z^2 ≤ (1488189/500000 : ℝ)^2 := by nlinarith [sq_nonneg ((1488189/500000 : ℝ)-x.z)]
  norm_num [coreZH,witnessRates]
  constructor <;> nlinarith
theorem high_energy_row_bound (i : Fin 4) :
    highLeft i*(∑ j : Fin 4, highComparison i j*highRight j)+
      highRight i*(∑ j : Fin 4, highComparison j i*highLeft j) ≤
        -(1/100:ℝ)*(highLeft i*highRight i) := by
  fin_cases i <;> norm_num [highLeft,highRight,highComparison,Fin.sum_univ_succ]

end CoreCouplingCAC
