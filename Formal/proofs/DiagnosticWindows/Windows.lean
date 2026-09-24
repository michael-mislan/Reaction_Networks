import proofs.DiagnosticWindows.Main
import proofs.DiagnosticWindows.WindowCertificates
namespace DiagnosticWindows
open FiniteCopy

theorem kernel6_uncalled_decay (x : Fin 6) : kernel6.step uncalled x ≤ uncalled x := by
  fin_cases x <;> norm_num [kernel6,birthKernel,FiniteKernel.step,uncalled,rates6,Fin.sum_univ_succ]
theorem survival6_antitone (x : Fin 6) : Antitone (fun t : NNReal => kernel6.poissonized t uncalled x) := by
  intro s t hst
  change kernel6.poissonized t uncalled x ≤ kernel6.poissonized s uncalled x
  rw [capacity6_survival,capacity6_survival]
  exact spectral_antitone kernel6 uncalled modes6 eigen6 capacity6_sum
    capacity6_eigen kernel6_uncalled_decay x s.property t.property hst
theorem blank6_monotone : Monotone blank6 := by
  intro s t hst
  have hm := survival6_antitone 0 (mul_le_mul_of_nonneg_left hst (by positivity : (0:NNReal) ≤ 5/2))
  unfold blank6
  linarith
theorem loaded6_antitone (load : NNReal) : Antitone (fun t : NNReal => loadedSurvival kernel6 load ((5/2)*t)) := by
  intro s t hst
  unfold loadedSurvival
  apply Summable.tsum_le_tsum
  · intro n
    exact mul_le_mul_of_nonneg_left
      (survival6_antitone (loadIndex n)
        (mul_le_mul_of_nonneg_left hst (by positivity : (0:NNReal) ≤ 5/2)))
      (poissonWeight_nonneg load n)
  · exact loading_summable kernel6 load ((5/2)*t)
  · exact loading_summable kernel6 load ((5/2)*s)
theorem miss6_antitone : Antitone miss6 := loaded6_antitone 4

theorem kernel7_uncalled_decay (x : Fin 6) : kernel7.step uncalled x ≤ uncalled x := by
  fin_cases x <;> norm_num [kernel7,birthKernel,FiniteKernel.step,uncalled,rates7,Fin.sum_univ_succ]
theorem survival7_antitone (x : Fin 6) : Antitone (fun t : NNReal => kernel7.poissonized t uncalled x) := by
  intro s t hst
  change kernel7.poissonized t uncalled x ≤ kernel7.poissonized s uncalled x
  rw [capacity7_survival,capacity7_survival]
  exact spectral_antitone kernel7 uncalled modes7 eigen7 capacity7_sum
    capacity7_eigen kernel7_uncalled_decay x s.property t.property hst
theorem blank7_monotone : Monotone blank7 := by
  intro s t hst
  have hm := survival7_antitone 0 (mul_le_mul_of_nonneg_left hst (by positivity : (0:NNReal) ≤ 5/2))
  unfold blank7
  linarith
theorem loaded7_antitone (load : NNReal) : Antitone (fun t : NNReal => loadedSurvival kernel7 load ((5/2)*t)) := by
  intro s t hst
  unfold loadedSurvival
  apply Summable.tsum_le_tsum
  · intro n
    exact mul_le_mul_of_nonneg_left
      (survival7_antitone (loadIndex n)
        (mul_le_mul_of_nonneg_left hst (by positivity : (0:NNReal) ≤ 5/2)))
      (poissonWeight_nonneg load n)
  · exact loading_summable kernel7 load ((5/2)*t)
  · exact loading_summable kernel7 load ((5/2)*s)
theorem miss7_antitone : Antitone miss7 := loaded7_antitone 4

theorem kernel8_uncalled_decay (x : Fin 6) : kernel8.step uncalled x ≤ uncalled x := by
  fin_cases x <;> norm_num [kernel8,birthKernel,FiniteKernel.step,uncalled,rates8,Fin.sum_univ_succ]
theorem survival8_antitone (x : Fin 6) : Antitone (fun t : NNReal => kernel8.poissonized t uncalled x) := by
  intro s t hst
  change kernel8.poissonized t uncalled x ≤ kernel8.poissonized s uncalled x
  rw [capacity8_survival,capacity8_survival]
  exact spectral_antitone kernel8 uncalled modes8 eigen8 capacity8_sum
    capacity8_eigen kernel8_uncalled_decay x s.property t.property hst
theorem blank8_monotone : Monotone blank8 := by
  intro s t hst
  have hm := survival8_antitone 0 (mul_le_mul_of_nonneg_left hst (by positivity : (0:NNReal) ≤ 5/2))
  unfold blank8
  linarith
theorem loaded8_antitone (load : NNReal) : Antitone (fun t : NNReal => loadedSurvival kernel8 load ((5/2)*t)) := by
  intro s t hst
  unfold loadedSurvival
  apply Summable.tsum_le_tsum
  · intro n
    exact mul_le_mul_of_nonneg_left
      (survival8_antitone (loadIndex n)
        (mul_le_mul_of_nonneg_left hst (by positivity : (0:NNReal) ≤ 5/2)))
      (poissonWeight_nonneg load n)
  · exact loading_summable kernel8 load ((5/2)*t)
  · exact loading_summable kernel8 load ((5/2)*s)
theorem miss8_antitone : Antitone miss8 := loaded8_antitone 4

theorem kernel9_uncalled_decay (x : Fin 6) : kernel9.step uncalled x ≤ uncalled x := by
  fin_cases x <;> norm_num [kernel9,birthKernel,FiniteKernel.step,uncalled,rates9,Fin.sum_univ_succ]
theorem survival9_antitone (x : Fin 6) : Antitone (fun t : NNReal => kernel9.poissonized t uncalled x) := by
  intro s t hst
  change kernel9.poissonized t uncalled x ≤ kernel9.poissonized s uncalled x
  rw [capacity9_survival,capacity9_survival]
  exact spectral_antitone kernel9 uncalled modes9 eigen9 capacity9_sum
    capacity9_eigen kernel9_uncalled_decay x s.property t.property hst
theorem blank9_monotone : Monotone blank9 := by
  intro s t hst
  have hm := survival9_antitone 0 (mul_le_mul_of_nonneg_left hst (by positivity : (0:NNReal) ≤ 5/2))
  unfold blank9
  linarith
theorem loaded9_antitone (load : NNReal) : Antitone (fun t : NNReal => loadedSurvival kernel9 load ((5/2)*t)) := by
  intro s t hst
  unfold loadedSurvival
  apply Summable.tsum_le_tsum
  · intro n
    exact mul_le_mul_of_nonneg_left
      (survival9_antitone (loadIndex n)
        (mul_le_mul_of_nonneg_left hst (by positivity : (0:NNReal) ≤ 5/2)))
      (poissonWeight_nonneg load n)
  · exact loading_summable kernel9 load ((5/2)*t)
  · exact loading_summable kernel9 load ((5/2)*s)
theorem miss9_antitone : Antitone miss9 := loaded9_antitone 4

theorem kernel10_uncalled_decay (x : Fin 6) : kernel10.step uncalled x ≤ uncalled x := by
  fin_cases x <;> norm_num [kernel10,birthKernel,FiniteKernel.step,uncalled,rates10,Fin.sum_univ_succ]
theorem survival10_antitone (x : Fin 6) : Antitone (fun t : NNReal => kernel10.poissonized t uncalled x) := by
  intro s t hst
  change kernel10.poissonized t uncalled x ≤ kernel10.poissonized s uncalled x
  rw [capacity10_survival,capacity10_survival]
  exact spectral_antitone kernel10 uncalled modes10 eigen10 capacity10_sum
    capacity10_eigen kernel10_uncalled_decay x s.property t.property hst
theorem blank10_monotone : Monotone blank10 := by
  intro s t hst
  have hm := survival10_antitone 0 (mul_le_mul_of_nonneg_left hst (by positivity : (0:NNReal) ≤ 5/2))
  unfold blank10
  linarith
theorem loaded10_antitone (load : NNReal) : Antitone (fun t : NNReal => loadedSurvival kernel10 load ((5/2)*t)) := by
  intro s t hst
  unfold loadedSurvival
  apply Summable.tsum_le_tsum
  · intro n
    exact mul_le_mul_of_nonneg_left
      (survival10_antitone (loadIndex n)
        (mul_le_mul_of_nonneg_left hst (by positivity : (0:NNReal) ≤ 5/2)))
      (poissonWeight_nonneg load n)
  · exact loading_summable kernel10 load ((5/2)*t)
  · exact loading_summable kernel10 load ((5/2)*s)
theorem miss10_antitone : Antitone miss10 := loaded10_antitone 4

theorem capacity6_no_deadline (t : NNReal) : ¬(blank6 t ≤ 1/100 ∧ miss6 t ≤ 1/20) := by
  intro h
  rcases le_total t 4 with ht | ht
  · have hm := miss6_antitone ht
    have he : (1:ℝ)/20 < miss6 4 := by simpa [miss6] using r6_miss_bound
    linarith [h.2]
  · have hb := blank6_monotone ht
    linarith [r6_blank_bound,h.1]
theorem capacity7_no_deadline (t : NNReal) : ¬(blank7 t ≤ 1/100 ∧ miss7 t ≤ 1/20) := by
  intro h
  rcases le_total t (367/100) with ht | ht
  · have hm := miss7_antitone ht
    have he : (1:ℝ)/20 < miss7 (367/100) := by simpa [miss7] using r7_miss_bound
    linarith [h.2]
  · have hb := blank7_monotone ht
    linarith [r7_blank_bound,h.1]
theorem capacity8_grid_impossible (k : ℕ) :
    ¬(blank8 ((k:NNReal)/10) ≤ 1/100 ∧ miss8 ((k:NNReal)/10) ≤ 1/20) := by
  intro h
  by_cases hk : k ≤ 34
  · have ht : (k:NNReal)/10 ≤ 17/5 := by
      have hcast : (k:NNReal) ≤ 34 := by exact_mod_cast hk
      linarith
    have hm := miss8_antitone ht
    have he : (1:ℝ)/20 < miss8 (17/5) := by simpa [miss8] using r8early_miss_bound
    linarith [h.2]
  · have hk2 : 35 ≤ k := by omega
    have ht : (7:NNReal)/2 ≤ (k:NNReal)/10 := by
      have hcast : (35:NNReal) ≤ k := by exact_mod_cast hk2
      linarith
    have hb := blank8_monotone ht
    linarith [r8late_blank_bound,h.1]
theorem capacity10_interval (t : NNReal) (ht0 : 63/20 ≤ t) (ht1 : t ≤ 33/10) :
    blank10 t ≤ 1/100 ∧ miss10 t ≤ 1/20 := by
  exact ⟨(blank10_monotone ht1).trans interval_late_blank_bound,
    (miss10_antitone ht0).trans (by simpa [miss10] using interval_early_miss_bound)⟩
theorem minimum_capacity_certificates :
    (∀ t : NNReal, ¬(blank5 t ≤ 1/100 ∧ miss5 t ≤ 1/20)) ∧
    (∀ t : NNReal, ¬(blank6 t ≤ 1/100 ∧ miss6 t ≤ 1/20)) ∧
    (∀ t : NNReal, ¬(blank7 t ≤ 1/100 ∧ miss7 t ≤ 1/20)) ∧
    (blank8 (69/20) ≤ 1/100 ∧ miss8 (69/20) ≤ 1/20) ∧
    (∀ k : ℕ, ¬(blank8 ((k:NNReal)/10) ≤ 1/100 ∧ miss8 ((k:NNReal)/10) ≤ 1/20)) ∧
    (blank9 (33/10) ≤ 1/100 ∧ miss9 (33/10) ≤ 1/20) :=
  ⟨capacity5_no_deadline,capacity6_no_deadline,capacity7_no_deadline,
    ⟨r8_blank_bound,by simpa [miss8] using r8_miss_bound⟩,capacity8_grid_impossible,⟨r9_blank_bound,by simpa [miss9] using r9_miss_bound⟩⟩
end DiagnosticWindows
