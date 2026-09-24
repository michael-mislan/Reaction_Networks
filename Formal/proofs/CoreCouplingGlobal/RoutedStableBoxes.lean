import proofs.CoreCouplingGlobal.RoutedLocalDynamics
import proofs.CoreCouplingCAC.InitialSets

namespace CoreCouplingGlobal
open CoreCouplingCAC

noncomputable def routedLowLower : State := ⟨324/25,1001/50,2489/2500,447/50⟩
noncomputable def routedLowUpper : State := ⟨1299/100,501/25,249/250,449/50⟩
noncomputable def routedLowComparison : Fin 4 → Fin 4 → ℝ :=
  ![![(-312580919/312500000:ℝ),(1350349/5000000000:ℝ),(0:ℝ),(0:ℝ)],![(5001300299/5000000000:ℝ),(-3744834919/1250000000:ℝ),(501/25:ℝ),(0:ℝ)],![(1:ℝ),(499/250:ℝ),(-2199238999/50000000:ℝ),(3:ℝ)],![(0:ℝ),(0:ℝ),(2498/125:ℝ),(-20001/10000:ℝ)]]

theorem routedLow_energy_row (i : Fin 4) :
    lowLeft i*(∑ j : Fin 4, routedLowComparison i j*lowRight j)+
      lowRight i*(∑ j : Fin 4, routedLowComparison j i*lowLeft j) ≤
        -(1/100:ℝ)*(lowLeft i*lowRight i) := by
  fin_cases i <;> norm_num [lowLeft,lowRight,routedLowComparison,Fin.sum_univ_succ]

theorem routedLow_jacobian_domination (e g : ℝ)
    (he : (999/100000000:ℝ) ≤ e) (heu : e ≤ 1001/100000000)
    (hg : (999999/1000000:ℝ) ≤ g) (hgu : g ≤ 1)
    (x : State) (hx : InBox x routedLowLower routedLowUpper) :
    (∀ i, routedJacobian e g (transform x) i i ≤ routedLowComparison i i) ∧
    (∀ i j, i ≠ j → |routedJacobian e g (transform x) i j| ≤ routedLowComparison i j) := by
  rcases hx with ⟨ha,hau,hb,hbu,hz,hzu,hH,hHu⟩
  norm_num [routedLowLower,routedLowUpper] at ha hau hb hbu hz hzu hH hHu
  have hea : (999/100000000)*(324/25) ≤ e*x.A := mul_le_mul he ha (by norm_num) (by linarith)
  have heau : e*x.A ≤ (1001/100000000)*(1299/100) := mul_le_mul heu hau (by linarith) (by norm_num)
  have hgz : (999999/1000000)*(2489/2500) ≤ g*x.z := mul_le_mul hg hz (by norm_num) (by linarith)
  have hgzu : g*x.z ≤ 249/250 := by
    have h := mul_le_mul hgu hzu (by linarith) (by norm_num : (0:ℝ) ≤ 1)
    simpa using h
  have hgb : (999999/1000000)*(1001/50) ≤ g*x.B := mul_le_mul hg hb (by norm_num) (by linarith)
  have hgbu : g*x.B ≤ 501/25 := by
    have h := mul_le_mul hgu hbu (by linarith) (by norm_num : (0:ℝ) ≤ 1)
    simpa using h
  constructor
  · intro i
    fin_cases i <;> norm_num [routedJacobian,transform,routedLowComparison,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
    all_goals nlinarith
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try exact (hij rfl).elim
    all_goals norm_num [routedJacobian,transform,routedLowComparison,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
    all_goals try simp only [abs_le]
    all_goals try rw [abs_of_nonneg (show 0 ≤ e by linarith)]
    all_goals try rw [abs_of_nonneg (show 0 ≤ g by linarith)]
    all_goals try rw [abs_of_nonneg (show 0 ≤ x.B by linarith)]
    all_goals try rw [abs_of_nonneg (show 0 ≤ 1+2*x.A by linarith)]
    all_goals try rw [abs_of_nonneg (show 0 ≤ 1+x.z by linarith)]
    all_goals try apply And.intro
    all_goals nlinarith

theorem routedLow_box_positive (x : State) (hx : InBox x routedLowLower routedLowUpper) : x.Positive := by
  rcases hx with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [routedLowLower,routedLowUpper] at *
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem routedLow_box_norm (x : State) (hx : InBox x routedLowLower routedLowUpper) : ‖transform x‖ ≤ 100 := by
  rcases hx with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [routedLowLower,routedLowUpper] at *
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 100)).2
  intro i
  fin_cases i <;> simp [transform,Real.norm_eq_abs,abs_le] <;> constructor <;> linarith

noncomputable def routedHighLower : State := ⟨523/25,241/20,29761/10000,816/25⟩
noncomputable def routedHighUpper : State := ⟨524/25,1207/100,29767/10000,327/10⟩
noncomputable def routedHighComparison : Fin 4 → Fin 4 → ℝ :=
  ![![(-1250522477/1250000000:ℝ),(1074073/2500000000:ℝ),(0:ℝ),(0:ℝ)],![(312631131/312500000:ℝ),(-9953049991/2000000000:ℝ),(1207/100:ℝ),(0:ℝ)],![(1:ℝ),(39767/10000:ℝ),(-1037175759/20000000:ℝ),(3:ℝ)],![(0:ℝ),(0:ℝ),(69767/2500:ℝ),(-20001/10000:ℝ)]]

theorem routedHigh_energy_row (i : Fin 4) :
    highLeft i*(∑ j : Fin 4, routedHighComparison i j*highRight j)+
      highRight i*(∑ j : Fin 4, routedHighComparison j i*highLeft j) ≤
        -(1/100:ℝ)*(highLeft i*highRight i) := by
  fin_cases i <;> norm_num [highLeft,highRight,routedHighComparison,Fin.sum_univ_succ]

theorem routedHigh_jacobian_domination (e g : ℝ)
    (he : (999/100000000:ℝ) ≤ e) (heu : e ≤ 1001/100000000)
    (hg : (999999/1000000:ℝ) ≤ g) (hgu : g ≤ 1)
    (x : State) (hx : InBox x routedHighLower routedHighUpper) :
    (∀ i, routedJacobian e g (transform x) i i ≤ routedHighComparison i i) ∧
    (∀ i j, i ≠ j → |routedJacobian e g (transform x) i j| ≤ routedHighComparison i j) := by
  rcases hx with ⟨ha,hau,hb,hbu,hz,hzu,hH,hHu⟩
  norm_num [routedHighLower,routedHighUpper] at ha hau hb hbu hz hzu hH hHu
  have hea : (999/100000000)*(523/25) ≤ e*x.A := mul_le_mul he ha (by norm_num) (by linarith)
  have heau : e*x.A ≤ (1001/100000000)*(524/25) := mul_le_mul heu hau (by linarith) (by norm_num)
  have hgz : (999999/1000000)*(29761/10000) ≤ g*x.z := mul_le_mul hg hz (by norm_num) (by linarith)
  have hgzu : g*x.z ≤ 29767/10000 := by
    have h := mul_le_mul hgu hzu (by linarith) (by norm_num : (0:ℝ) ≤ 1)
    simpa using h
  have hgb : (999999/1000000)*(241/20) ≤ g*x.B := mul_le_mul hg hb (by norm_num) (by linarith)
  have hgbu : g*x.B ≤ 1207/100 := by
    have h := mul_le_mul hgu hbu (by linarith) (by norm_num : (0:ℝ) ≤ 1)
    simpa using h
  constructor
  · intro i
    fin_cases i <;> norm_num [routedJacobian,transform,routedHighComparison,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
    all_goals nlinarith
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try exact (hij rfl).elim
    all_goals norm_num [routedJacobian,transform,routedHighComparison,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
    all_goals try simp only [abs_le]
    all_goals try rw [abs_of_nonneg (show 0 ≤ e by linarith)]
    all_goals try rw [abs_of_nonneg (show 0 ≤ g by linarith)]
    all_goals try rw [abs_of_nonneg (show 0 ≤ x.B by linarith)]
    all_goals try rw [abs_of_nonneg (show 0 ≤ 1+2*x.A by linarith)]
    all_goals try rw [abs_of_nonneg (show 0 ≤ 1+x.z by linarith)]
    all_goals try apply And.intro
    all_goals nlinarith

theorem routedHigh_box_positive (x : State) (hx : InBox x routedHighLower routedHighUpper) : x.Positive := by
  rcases hx with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [routedHighLower,routedHighUpper] at *
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem routedHigh_box_norm (x : State) (hx : InBox x routedHighLower routedHighUpper) : ‖transform x‖ ≤ 100 := by
  rcases hx with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  norm_num [routedHighLower,routedHighUpper] at *
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 100)).2
  intro i
  fin_cases i <;> simp [transform,Real.norm_eq_abs,abs_le] <;> constructor <;> linarith

end CoreCouplingGlobal
